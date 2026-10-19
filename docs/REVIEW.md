# Review of the VRPTW model

This document records the review of the original `VRPTW.mod`/`VRPTW.dat`,
the changes made as a result, and suggestions that were **not** applied
because they change the scope of the project.

## 1. Defects found and fixed

### 1.1 The sample data used a customer as the returning depot (data bug)

Node `6` (the returning depot, `CustomersNumber + 1`) had coordinates
`(65, 20)` and a service time of `10`. Those values are Solomon R101 customer
data, not a copy of the depot at `(35, 35)`. Consequences:

* every route ended 33.5 units away from the real depot, so the reported
  distance was not the distance of a closed tour;
* every *idle* vehicle paid 33.5 for the phantom trip `0 -> 6`; with five
  vehicles the objective was inflated by 100.5 (231.7 instead of the correct
  value for that fragment).

`VRPTW.dat` now contains the depot and the first five customers of R101 with
their real time windows, and node `6` is a copy of node `0`. The optimum is
156.2 using two vehicles (verified independently by the brute-force solver).
`Instance.validate()` / `python -m vrptw validate` reject data where the end
depot is not a copy of the depot.

### 1.2 Arcs into the depot and out of the end depot were not forbidden

Only self loops were fixed to zero. Arcs `i -> 0` and `n+1 -> j` were left
free; the time constraints happened to make most of them useless, but
`0 -> n+1 -> 0` with zero travel time was feasible and would have been printed
as a bogus leg. All such arcs, and arcs that are incompatible with the time
windows (`a_i + t_ij > b_j`), are now fixed to zero (`ctForbiddenArc`).

### 1.3 Service start times were declared integer

`dvar int s[...]` forces integral start times although distances have one
decimal. This can make feasible instances infeasible (a vehicle arriving at
`b_j + 0.3` and being forced to round up past the deadline) and makes the
branch-and-bound work harder. `s` is now continuous with the time window as
its bounds (`dvar float s[k][i] in LBTW[i]..UBTW[i]`), which also removes the
35 explicit window constraints.

### 1.4 One global big-M for every arc

`maxTimeSpentBetweenTwoCustomers` was the largest `b_i + t_ij - a_j` over all
pairs and was used in every time constraint. The LP relaxation of a big-M
constraint is only as tight as the smallest valid `M`, so the model now uses
the per-arc value `M_ij = max(0, b_i + t_ij - a_j)` (`BigM[i][j]`). This is the
standard tightening from the VRPTW literature and is free.

### 1.5 Redundant constraint

`sum(k, j) x[k][0][j] <= v` can never be violated: `ctLeaveDepot` already
forces each vehicle to leave exactly once, so the sum is always exactly `v`.
Removed.

### 1.6 Distance computation in a script block

The distance and time matrices were filled in an `execute` block with
JavaScript. OPL can express them as generic array initialisers, which is
shorter, type-checked and visible to the IDE. The truncation to one decimal
(`floor(10·d)/10`, the Solomon convention) is kept and documented.

### 1.7 Output

`DISPLAY` listed the selected arcs in index order, which is hard to read for
more than a couple of customers. It now prints the objective, the number of
vehicles used and each route in visiting order with the start-of-service time
at every stop, and marks idle vehicles.

## 2. Improvements added

* **Symmetry breaking.** Vehicles are identical, so any permutation of the
  vehicle indices is an equivalent solution. `ctSymmetry` forces idle vehicles
  to take the highest indices, which removes a factorial number of equivalent
  branches. The test-suite checks it does not change the optimum.
* **Named constraints and `dexpr`s** (`TotalDistance`, `VehiclesUsed`) to make
  the IDE's conflict refiner and solution browser useful.
* **Python port** (`vrptw/model.py`) of the formulation with docplex. It
  creates variables only for the allowed arcs, mirrors each OPL constraint
  and is tested against a brute-force solver on the sample instance and on
  random small instances.
* **Data tooling**: a `.dat` reader/writer, a Solomon benchmark reader and
  converter, an instance validator and a solver-independent solution checker.
* **Tests and CI**: 41 tests (`python -m unittest`) run on Python 3.10–3.14
  with the CPLEX Community Edition from PyPI, plus `ruff` linting.

## 3. Versions

| Component | Version used |
| --- | --- |
| IBM ILOG CPLEX Optimization Studio | 22.2 (GA May 2026); the model needs nothing newer than 12.x |
| `cplex` (PyPI, Community Edition) | 22.2.0.1 (wheels for Python 3.10–3.14) |
| `docplex` | 2.32 |
| Python | 3.10–3.14 |
| GitHub Actions | `actions/checkout@v7`, `actions/setup-python@v7` |

## 4. Suggestions not applied

These are worth considering depending on where the project goes; each one
changes the model's scope or its readability trade-offs, so they are left as
suggestions.

1. **Sparse arc set in OPL.** Declaring `tuple Arc {int i; int j;}`, a set
   `Arcs = {<i,j> | i,j in Nodes : Allowed[i][j] == 1}` and
   `dvar boolean x[Vehicles][Arcs]` avoids creating the forbidden variables at
   all instead of fixing them to zero. CPLEX presolve removes the fixed
   variables anyway, so the solve is the same, but the generated model is
   smaller and tighter time windows prune more. The dense form was kept
   because it is easier to read; the Python port already uses the sparse form.
2. **Two-index formulation.** With identical vehicles the vehicle index is
   unnecessary: use `x[i][j]`, `s[i]` and a load variable `u[i]` with
   Miller–Tucker–Zemlin style capacity propagation
   (`u_i + q_j - Q(1 - x_ij) ≤ u_j`). This divides the number of variables by
   `v`, removes the vehicle symmetry entirely and is the formulation of
   choice for anything beyond a few customers. The three-index form was kept
   because it is the one the repository documents and it supports
   heterogeneous fleets.
3. **Hierarchical objective.** The Solomon benchmark convention minimises the
   number of vehicles first and the distance second. In OPL this is
   `minimize staticLex(VehiclesUsed, TotalDistance);` (both `dexpr`s already
   exist), or a weighted sum `BigWeight * VehiclesUsed + TotalDistance`.
4. **CP Optimizer model.** For larger instances or richer side constraints
   (multiple time windows, driver breaks, precedence) a CP Optimizer model
   with interval variables, one `sequence` per vehicle, `noOverlap` with a
   transition-distance matrix and `endBeforeStart` constraints usually finds
   good solutions much faster than the MIP, at the cost of weaker optimality
   proofs. OPL supports both engines in the same project.
5. **Exact methods for benchmark sizes.** The compact MIP solves instances of
   roughly 15–25 customers. Solomon's 100-customer instances require
   branch-and-price (set-partitioning master problem, elementary shortest
   path pricing with resource constraints); docplex is a reasonable base for
   the master problem.
6. **Valid inequalities and preprocessing.** Time window tightening
   (`a_i := max(a_i, a_0 + t_0i)`, `b_i := min(b_i, b_{n+1} - t_i,n+1)`),
   two-path cuts and the capacity cut `Σ_j x_k0j ≥ ⌈Σ q_i / Q⌉` strengthen
   the LP bound considerably.
7. **Warm start.** A sweep or nearest-neighbour heuristic provides a feasible
   incumbent; passing it to CPLEX (`cplex.addMIPStart` in OPL script,
   `Model.add_mip_start` in docplex) prunes the tree early.
8. **Solver settings.** For the MIP, `cplex.tilim`, `cplex.epgap` and
   `cplex.mipemphasis = 1` (feasibility) are the usual knobs; they can be set
   in an `execute { }` block before the model or in the IDE run
   configuration.
