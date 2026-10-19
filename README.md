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
| `VRPTW.mod` | The OPL model (the reference implementation). |
| `VRPTW.dat` | Sample instance: the depot and the first five customers of Solomon's R101. |
| `vrptw/` | Python package: `.dat`/Solomon readers, the docplex port of the model, a feasibility checker and a brute-force reference solver. |
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

Open the project in the IDE and run the default configuration, or use the
command line interface:

```bash
oplrun VRPTW.mod VRPTW.dat
```

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
python -m vrptw validate VRPTW.dat             # check the data for consistency
python -m vrptw solve VRPTW.dat                # solve with CPLEX through docplex
python -m vrptw solve VRPTW.dat --brute-force  # exhaustive reference solver (tiny instances)
python -m vrptw convert R101.txt -o R101_25.dat --customers 25   # Solomon file -> .dat
```

`vrptw` is also installed as a console script by `pip install -e .`.
From Python:

```python
from vrptw import read_dat, check_solution
from vrptw.model import solve

inst = read_dat("VRPTW.dat")
solution = solve(inst)
print(solution.distance, solution.routes)   # 156.2 ((5, 3, 1), (2, 4), (), (), ())
assert check_solution(inst, solution.routes) == []
```

## The formulation

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
