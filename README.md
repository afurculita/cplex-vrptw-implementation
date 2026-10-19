# cplex-vrptw-implementation

[![CI](https://github.com/afurculita/cplex-vrptw-implementation/actions/workflows/ci.yml/badge.svg)](https://github.com/afurculita/cplex-vrptw-implementation/actions/workflows/ci.yml)

A mixed-integer programming model of the **Vehicle Routing Problem with Time
Windows (VRPTW)** written in OPL for IBM ILOG CPLEX Optimization Studio, plus a
Python port of the same formulation (docplex), data tooling and a test-suite.

A fleet of identical vehicles based at a depot must serve every customer
exactly once, within the customer's time window, without exceeding the vehicle
capacity, while minimising the total distance travelled.

## Repository layout

| Path | Purpose |
| --- | --- |
| `VRPTW.mod` | Three-index MIP (one arc variable per vehicle): the original formulation, reviewed and tightened. |
| `VRPTW2.mod` | Two-index MIP with a sparse arc set and MTZ load variables: `v` times fewer variables, no vehicle symmetry. Recommended for identical vehicles. Minimises vehicles first, then distance. |
| `VRPTW_CP.mod` | CP Optimizer model (interval and sequence variables). Finds good solutions on instances far too large for the MIPs. Not covered by the test-suite, see the note in the file. |
| `VRPTW.dat` | Sample instance: the depot and the first five customers of Solomon's R101. |
| `vrptw/` | Python package: `.dat`/Solomon readers, time-window tightening, a construction heuristic, docplex ports of both MIPs (warm start, lexicographic objective, callback-separated cuts), a branch-and-price solver, a feasibility checker and a brute-force reference solver. |
| `tests/` | `unittest` suite covering the data, the checker, the CLI and the model (solved with CPLEX). |
| `docs/REVIEW.md` | Review of the original model, the fixes made and suggestions for further improvements. |
| `.oplproject`, `.project` | CPLEX Optimization Studio IDE project files. |

## Requirements

* **OPL model:** IBM ILOG CPLEX Optimization Studio 22.2 (the current release;
  any 12.x/20.x/22.x version should work, the model uses no recent features).
* **Python tooling:** Python 3.10 or newer. Solving with Python additionally
  needs `cplex` and `docplex`. The free [CPLEX Community Edition on
  PyPI](https://pypi.org/project/cplex/) (22.2, limited to 1000 variables and
  constraints) is enough for the sample instance and the tests; a full CPLEX
  installation removes that limit.

```bash
pip install -e ".[solver]"   # or: pip install cplex docplex
```

## Usage

### OPL (CPLEX Optimization Studio)

Open the project in the IDE and pick one of the three run configurations
(three-index MIP, two-index MIP, CP Optimizer), or use the command line:

```bash
oplrun VRPTW.mod VRPTW.dat      # three-index MIP, minimises distance
oplrun VRPTW2.mod VRPTW.dat     # two-index MIP, fewest vehicles then distance
oplrun VRPTW_CP.mod VRPTW.dat   # CP Optimizer
```

All three models read the same data, tighten the time windows in
preprocessing and set a 600 s time limit in their `PARAMS` block (edit it
there or override it in the IDE run configuration).

Output of the sample instance:

```
Total distance: 156.2
Vehicles used: 2 of 5
vehicle 1: 0@0 -> 5@34 -> 3@116 -> 1@161 -> 6@186.2
vehicle 2: 0@0 -> 2@50 -> 4@149 -> 6@184
vehicle 3: idle
vehicle 4: idle
vehicle 5: idle
```

Each stop is printed as `node@start-of-service-time`; node `6` is the copy of
the depot at the end of every route.

### Python

```bash
python -m vrptw validate VRPTW.dat                      # check the data for consistency
python -m vrptw solve VRPTW.dat                         # two-index MIP with CPLEX (docplex)
python -m vrptw solve VRPTW.dat --formulation three-index
python -m vrptw solve VRPTW.dat --objective lex         # fewest vehicles first, then distance
python -m vrptw solve VRPTW.dat --time-limit 60 --mip-gap 0.01
python -m vrptw solve VRPTW.dat --cuts                  # branch-and-cut: capacity and 2-path cuts in a callback
python -m vrptw solve VRPTW.dat --method branch-and-price
python -m vrptw solve VRPTW.dat --heuristic             # construction heuristic only, no CPLEX
python -m vrptw solve VRPTW.dat --brute-force           # exhaustive reference solver (tiny instances)
python -m vrptw convert R101.txt -o R101_25.dat --customers 25   # Solomon file -> .dat
```

`solve` tightens the time windows, builds the model with the tightest
per-arc big-M, adds the capacity cut, warm-starts CPLEX with the heuristic
solution and verifies the returned routes with the independent checker.
Each step can be switched off (`--no-preprocess`, `--no-warm-start`).
A `Statistics:` line reports nodes, time, gap and the number of cuts or
columns generated.

### Exact methods

| Method | Where | Best for |
| --- | --- | --- |
| Three-index MIP | `VRPTW.mod`, `--formulation three-index` | Small instances, heterogeneous fleets. |
| Two-index MIP | `VRPTW2.mod`, `--formulation two-index` (default) | Up to roughly 20–25 customers. |
| Branch-and-cut | `--cuts` | Same model with rounded capacity cuts and 2-path cuts separated on the LP relaxation in a CPLEX generic callback (`vrptw/cuts.py`). Strengthens the bound; note that any relaxation callback makes CPLEX fall back from dynamic search to traditional branch-and-bound. |
| Branch-and-price | `--method branch-and-price` | Set-partitioning master with ESPPRC pricing (`vrptw/branch_and_price.py`, `vrptw/pricing.py`); the LP bound is much tighter than the arc formulations', so it scales to larger instances with tight windows. Distance objective only. |

On random instances with 12, 15 and 20 customers all three exact methods
return the same optimum; the branch-and-price root bound was within 1.5 %
of the optimum on the 20-customer instance and within 6 % on the
15-customer one.

`vrptw` is also installed as a console script by `pip install -e .`.
From Python:

```python
from vrptw import read_dat, check_solution
from vrptw.model import solve

inst = read_dat("VRPTW.dat")
solution = solve(inst)
print(solution.distance, solution.routes)  # 156.2 ((5, 3, 1), (2, 4), (), (), ())
assert check_solution(inst, solution.routes) == []
```

## The formulations

Sets: vehicles `K = 1..v`, customers `C = 1..n`, nodes `N = 0..n+1` where `0` is
the depot and `n+1` is a copy of it. Data: demand `q_i`, capacity `Q`, time
window `[a_i, b_i]`, service time `σ_i`, distance `d_ij` (Euclidean, truncated
to one decimal as in the Solomon benchmarks) and travel time
`t_ij = d_ij + σ_i`.

Variables: `x_kij ∈ {0,1}` is 1 when vehicle `k` drives from `i` to `j`;
`s_ki ∈ [a_i, b_i]` is the time vehicle `k` starts service at `i`.

```
min  Σ_k Σ_ij d_ij x_kij

Σ_k Σ_j x_kij = 1                              ∀ i ∈ C        (serve each customer once)
Σ_i∈C Σ_j q_i x_kij ≤ Q                        ∀ k            (capacity)
Σ_j x_k0j = 1                                  ∀ k            (leave the depot; 0 -> n+1 = idle)
Σ_i x_kih = Σ_j x_khj                          ∀ k, h ∈ C     (flow conservation)
Σ_i x_ki,n+1 = 1                               ∀ k            (return to the depot)
s_ki + t_ij - M_ij (1 - x_kij) ≤ s_kj          ∀ k, (i,j) ∈ A (time propagation, M_ij = max(0, b_i + t_ij - a_j))
x_kij = 0                                      ∀ k, (i,j) ∉ A (forbidden arcs)
x_k,0,n+1 ≤ x_k+1,0,n+1                        ∀ k < v        (symmetry breaking: idle vehicles last)
```

`A` is the set of usable arcs: no self loops, nothing enters node `0`, nothing
leaves node `n+1`, and `a_i + t_ij ≤ b_j`. The time propagation constraints
make sub-tours impossible, so no explicit sub-tour elimination is needed.
Both MIPs add the capacity cut `Σ_j x_0j ≥ ⌈Σ q_i / Q⌉` and first tighten the
windows with `a_j := max(a_j, min_i(a_i + t_ij))`,
`b_j := min(b_j, max_k(b_k - t_jk))` (Desrochers, Desrosiers & Solomon 1992).

### Two-index formulation (`VRPTW2.mod`)

For identical vehicles the vehicle index is unnecessary. `x_ij ∈ {0,1}` says
whether some vehicle uses arc `(i, j)`, `s_i` is the start of service and
`u_i ∈ [q_i, Q]` the load of the vehicle after serving customer `i`:

```
lexmin ( Σ_j x_0j ,  Σ_ij d_ij x_ij )

Σ_i x_ij = 1,  Σ_j x_ij = 1                    ∀ i ∈ C        (degree)
Σ_j x_0j ≤ v                                   (fleet size)
s_i + t_ij - M_ij (1 - x_ij) ≤ s_j             ∀ (i,j) ∈ A    (time propagation)
u_i + q_j - Q (1 - x_ij) ≤ u_j                 ∀ (i,j) ∈ A, i,j ∈ C (load propagation)
```

On the sample instance the two-index model has 30 variables and 38
constraints against 130 and 145 for the three-index model.

### Branch-and-price (`vrptw/branch_and_price.py`)

The set-partitioning master selects routes `r` with cost `c_r`:

```
min  Σ_r c_r λ_r
Σ_r a_ir λ_r = 1      ∀ i ∈ C      (every customer on exactly one route)
Σ_r λ_r ≤ v                        (fleet)
λ_r ≥ 0
```

Columns are priced by an elementary shortest path problem with resource
constraints (time and load), solved by label setting with the
"unreachable customers" dominance rule. Branching is on arc flows
`x_ij = Σ_r a_ijr λ_r` (forbid the arc, or force it by forbidding all its
competitors), which keeps the pricing problem unchanged in structure. An
artificial column keeps every node's LP feasible.

`docs/REVIEW.md` explains the choices and lists alternatives.

## Data format

`VRPTW.dat` uses standard OPL syntax. `Demand` is indexed over the customers
`1..CustomersNumber`; the other arrays are indexed over all nodes
`0..CustomersNumber+1`, and node `CustomersNumber+1` **must be a copy of node
0** (same coordinates, same time window, zero service time). `python -m vrptw
validate` checks these rules. `python -m vrptw convert` produces a valid file
from any Solomon benchmark instance.

## Running the tests

```bash
python -m unittest discover -v
```

The model tests solve small instances with CPLEX and compare the result with
the brute-force solver; they are skipped automatically when `docplex`/`cplex`
are not installed. CI runs the suite on Python 3.10 through 3.14 and lints
with `ruff`.

## License

MIT, see `LICENSE`.
