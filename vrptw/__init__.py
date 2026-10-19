"""Vehicle Routing Problem with Time Windows (VRPTW) tooling.

The repository's reference implementation is the OPL model in ``VRPTW.mod``.
This package provides:

* :mod:`vrptw.data` -- an instance data class, a reader/writer for the OPL
  ``.dat`` format used by the model and a reader for Solomon benchmark files.
* :mod:`vrptw.model` -- the same three-index formulation written with the
  ``docplex`` Python API, so it can be solved and tested without the OPL IDE.
* :mod:`vrptw.verify` -- a solver-independent feasibility checker and a
  brute-force exact solver used as ground truth in the tests.
"""

from vrptw.data import Instance, read_dat, read_solomon, write_dat
from vrptw.verify import Route, Solution, brute_force, check_solution

__all__ = [
    "Instance",
    "Route",
    "Solution",
    "brute_force",
    "check_solution",
    "read_dat",
    "read_solomon",
    "write_dat",
]

__version__ = "1.0.0"
