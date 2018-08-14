export
    SDPDecompMergePowerModel, SDPDecompMergeForm,
    SDPDecompSOCPowerModel, SDPDecompSOCForm

""
abstract type SDPDecompMergeForm <: AbstractWRMForm end

""
abstract type SDPDecompSOCForm <: AbstractWRMForm end

""
const SDPDecompMergePowerModel = GenericPowerModel{SDPDecompMergeForm}

""
const SDPDecompSOCPowerModel = GenericPowerModel{SDPDecompSOCForm}

SDPDecompMergePowerModel(data::Dict{String,Any}; kwargs...) = GenericPowerModel(data, SDPDecompMergeForm; kwargs...)

SDPDecompSOCPowerModel(data::Dict{String,Any}; kwargs...) = GenericPowerModel(data, SDPDecompSOCForm; kwargs...)

function variable_voltage(pm::GenericPowerModel{SDPDecompMergeForm}; nw::Int=pm.cnw, cnd::Int=pm.ccnd, bounded=true)

    cadj, lookup_index = chordal_extension(pm)
    groups = maximal_cliques(cadj)
    lookup_bus_index = map(reverse, lookup_index)
    groups = [[lookup_bus_index[gi] for gi in g] for g in groups]
    groups = greedy_merge(groups)

    pm.ext[:SDconstraintDecomposition] = SDconstraintDecomposition(groups, cadj, lookup_index)

    voltage_product_groups =
        var(pm, nw, cnd)[:voltage_product_groups] =
        Vector{Dict{Symbol, Array{JuMP.Variable, 2}}}(length(groups))

    for (gidx, group) in enumerate(groups)
        n = length(group)
        voltage_product_groups[gidx] = Dict()
        voltage_product_groups[gidx][:WR] =
            var(pm, nw, cnd)[:voltage_product_groups][gidx][:WR] =
            @variable(pm.model, [1:n, 1:n], Symmetric,
                basename="$(nw)_$(cnd)_$(gidx)_WR")

        voltage_product_groups[gidx][:WI] =
            var(pm, nw, cnd)[:voltage_product_groups][gidx][:WI] =
            @variable(pm.model, [1:n, 1:n],
                basename="$(nw)_$(cnd)_$(gidx)_WI")
    end

    # voltage product bounds
    visited_buses = []
    visited_buspairs = []
    var(pm, nw, cnd)[:w] = Dict{Int,Any}()
    var(pm, nw, cnd)[:wr] = Dict{Tuple{Int,Int},Any}()
    var(pm, nw, cnd)[:wi] = Dict{Tuple{Int,Int},Any}()
    wr_min, wr_max, wi_min, wi_max = calc_voltage_product_bounds(ref(pm, nw, :buspairs), cnd)
    for (gidx, voltage_product_group) in enumerate(voltage_product_groups)
        WR, WI = voltage_product_group[:WR], voltage_product_group[:WI]
        group = groups[gidx]
        ng = length(group)

        # diagonal bounds
        for (group_idx, bus_id) in enumerate(group)
            # group_idx indexes into group
            # bus_id indexes into ref(pm, nw, :bus)
            bus = ref(pm, nw, :bus, bus_id)

            wr_ii = WR[group_idx, group_idx]

            if bounded
                setupperbound(wr_ii, (bus["vmax"][cnd])^2)
                setlowerbound(wr_ii, (bus["vmin"][cnd])^2)
            else
                setlowerbound(wr_ii, 0)
            end

            # for non-semidefinite constraints
            if !(bus_id in visited_buses)
                push!(visited_buses, bus_id)
                var(pm, nw, cnd, :w)[bus_id] = wr_ii
            end
        end

        # off-diagonal bounds
        offdiag_indices = [(i, j) for i in 1:ng, j in 1:ng if i != j]
        for (i, j) in offdiag_indices
            i_bus, j_bus = group[i], group[j]
            if (i_bus, j_bus) in ids(pm, nw, :buspairs)
                if bounded
                    setupperbound(WR[i, j], wr_max[i_bus, j_bus])
                    setlowerbound(WR[i, j], wr_min[i_bus, j_bus])

                    setupperbound(WI[i, j], wi_max[i_bus, j_bus])
                    setlowerbound(WI[i, j], wi_min[i_bus, j_bus])
                end

                # for non-semidefinite constraints
                if !((i_bus, j_bus) in visited_buspairs)
                    push!(visited_buspairs, (i_bus, j_bus))
                    var(pm, nw, cnd, :wr)[(i_bus, j_bus)] = WR[i, j]
                    var(pm, nw, cnd, :wi)[(i_bus, j_bus)] = WI[i, j]
                end
            end
        end
    end
end

function constraint_voltage(pm::GenericPowerModel{T}, nw::Int, cnd::Int) where T <: AbstractWRMForm
    pair_matrix(group) = [(i, j) for i in group, j in group]

    decomp = pm.ext[:SDconstraintDecomposition]
    groups = decomp.decomp
    voltage_product_groups = var(pm, nw, cnd)[:voltage_product_groups]

    # semidefinite constraint for each group in clique grouping
    for (gidx, voltage_product_group) in enumerate(voltage_product_groups)
        group = groups[gidx]
        ng = length(group)
        WR = voltage_product_group[:WR]
        WI = voltage_product_group[:WI]

        if T == SDPDecompSOCForm && ng == 2
            wr_ii = WR[1, 1]
            wr_jj = WR[2, 2]
            wr_ij = WR[1, 2]
            wi_ij = WI[1, 2]

            # rotated SOC form (Mosek says infeasible)
            # @constraint(pm.model, wr_ii - wr_jj >= norm([wr_ij, wi_ij]))

            # standard SOC form
            @constraint(pm.model, (wr_ii + wr_jj)/2 >= norm([(wr_ii - wr_jj)/2; wr_ij; wi_ij]))

            # apparently unnecessary
            # @constraint(pm.model, wr_ij == WR[2, 1])
        else
            @SDconstraint(pm.model, [WR WI; -WI WR] >= 0)
        end
    end

    # linking constraints
    tree = prim(overlap_graph(groups))
    overlapping_pairs = [ind2sub(tree, i) for i in find(tree)]
    for (i, j) in overlapping_pairs
        gi, gj = groups[i], groups[j]
        var_i, var_j = voltage_product_groups[i], voltage_product_groups[j]

        Gi, Gj = pair_matrix(gi), pair_matrix(gj)
        overlap_i, overlap_j = overlap_indices(Gi, Gj)
        indices = zip(overlap_i, overlap_j)
        for (idx_i, idx_j) in indices
            @constraint(pm.model, var_i[:WR][idx_i] == var_j[:WR][idx_j])
            @constraint(pm.model, var_i[:WI][idx_i] == var_j[:WI][idx_j])
        end
    end
end

# Old decomposition implementation: trust JuMP/solver to set up linking constraints
# function constraint_voltage(pm::GenericPowerModel{SDPDecompMergeForm}, nw::Int, cnd::Int)
#     WR = var(pm, nw, cnd)[:WR]
#     WI = var(pm, nw, cnd)[:WI]
#
#     cadj, lookup_index = chordal_extension(pm)
#     cliques = maximal_cliques(cadj)
#     clique_grouping = greedy_merge(cliques)
#     for group in clique_grouping
#         WRgroup = WR[group, group]
#         WIgroup = WI[group, group]
#         @SDconstraint(pm.model, [WRgroup WIgroup; -WIgroup WRgroup] >= 0)
#     end
# end

function merge_cost(groups, i, k)
    nvars(n::Integer) = n*(2*n + 1)
    nvars(g::Vector) = nvars(length(g))

    gi, gk = groups[i], groups[k]
    overlap = intersect(gi, gk)
    gnew = union(gi, gk)
    return nvars(gnew) - nvars(gi) - nvars(gk) - nvars(overlap)
end

function merge_groups!(groups, i, k)
    gi, gk = groups[i], groups[k]
    filter!(g -> g != gi && g != gk, groups)
    push!(groups, union(gi, gk))
end

"""
    merged_groups = greedy_merge(groups)
Greedily merge groups belonging to `groups`. Merge costs are computed by the function
`merge_cost`, which accepts `groups` and two group indices, and returns the change
in objective value associated with merging the two groups.

This function assumes that merge costs grow with increasing overlap between groups.
"""
function greedy_merge(groups::Vector{Vector{Int64}}, merge_cost::Function=merge_cost; nmerge=Inf, merge_2cliques=false)
    merged_groups = copy(groups)
    function stop_condition(delta, merges)
        if nmerge == Inf
            return delta >= 0
        else
            return merges == nmerge
        end
    end

    merges = 0
    stop_cond = false
    while !stop_cond
        T = prim(overlap_graph(merged_groups))
        potential_merges = [ind2sub(T, idx) for idx in find(T)]

        if !merge_2cliques
            # do not merge 2-vertex cliques
            idx_2cliques = find(length.(merged_groups).==2)
            filter!(m -> !(m[1] in idx_2cliques || m[2] in idx_2cliques), potential_merges)
        end

        length(potential_merges) == 0 && break
        merge_costs = [merge_cost(merged_groups, merge...) for merge in potential_merges]
        delta, merge_idx = findmin(merge_costs)
        if nmerge == Inf && delta == 0
            break
        end
        i, k = potential_merges[merge_idx]
        merge_groups!(merged_groups, i, k)
        merges += 1
        stop_cond = stop_condition(delta, merges)
    end
    return merged_groups
end

# function set_decomposition(pm::GenericPowerModel{T}) where T <: AbstractWRMForm
#     if T == SDPDecompForm
#         return
#     elseif T == SDPDecompMergeForm
#
