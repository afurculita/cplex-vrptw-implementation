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

## 4. Further improvements applied

The suggestions below were implemented after the review (in both the OPL
models and the Python port unless stated otherwise).

1. **Two-index formulation** (`VRPTW2.mod`, `--formulation two-index`,
   the Python default). Arc variables `x[i][j]` shared by all vehicles,
   Miller–Tucker–Zemlin load variables for the capacity, time propagation
   as before. `v` times fewer arc variables and no vehicle symmetry; on the
   sample instance 30 variables / 38 constraints instead of 130 / 145.
2. **Sparse arc set in OPL.** `VRPTW2.mod` declares `tuple Arc` and
   `{Arc} Arcs` filtered by the time windows, so forbidden arcs never get a
   variable. `VRPTW.mod` keeps the dense form (fixed to zero) for
   readability.
3. **Hierarchical objective.** `VRPTW2.mod` minimises
   `staticLex(VehiclesUsed, TotalDistance)`; the Python port offers
   `objective="lex"` through docplex's `minimize_static_lex`, and the
   brute-force solver can compute the same lexicographic optimum for the
   tests.
4. **Time-window tightening** (`vrptw/preprocess.py`, `execute
   TIGHTEN_TIME_WINDOWS` in both MIPs). Two necessary conditions are
   iterated to a fixed point. Tests check the optimum is preserved on random
   instances and that the reduction is idempotent.
5. **Capacity cut** `VehiclesUsed >= ceil(total demand / Capacity)` in both
   MIPs.
6. **Warm start** (`vrptw/heuristic.py`). A time-oriented nearest-neighbour
   construction followed by a relocate local search gives a feasible
   incumbent that is passed to CPLEX with `add_mip_start`. In OPL the same
   can be done with `cplex.addMIPStart` from a preprocessing script; it is
   not included because the heuristic is far easier to write and test in
   Python.
7. **Solver settings.** `execute PARAMS` blocks set `cplex.tilim`,
   `cplex.epgap`, `cplex.mipemphasis` and `cplex.threads` (CP: `TimeLimit`,
   `Workers`); the CLI exposes `--time-limit` and `--mip-gap`.
8. **CP Optimizer model** (`VRPTW_CP.mod`). Interval variables per visit,
   optional per-vehicle copies linked with `alternative`, one `sequence` per
   vehicle with `noOverlap` and a transition matrix of travel distances,
   `first`/`last` for the depots, the distance computed with `typeOfNext`.
   Times are scaled by 10 so they are integer. **Not executed here**: the
   Community Edition on PyPI ships no CP Optimizer engine, so this model is
   provided as a starting point and flagged as untested in its header.

## 5. Suggestions not applied

* **Branch-and-price.** Solomon's 100-customer instances need a
  set-partitioning master problem with an elementary shortest path pricing
  problem with resource constraints (ESPPRC). This is a project of its own
  (labelling algorithm, column management, branching rules) and is out of
  scope for a compact-model repository; the two-index model solves
  instances of roughly 15–25 customers and the CP model gives good
  heuristic solutions beyond that.
* **Stronger cuts** (two-path cuts, k-path cuts, subtour-elimination cuts
  separated in a callback) require a callback-driven branch-and-cut, which
  OPL does not expose; they could be added in the docplex port with CPLEX's
  generic callbacks.
