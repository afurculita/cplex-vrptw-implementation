"""End-to-end tests of the formulation, solved with CPLEX through docplex.

Skipped when ``docplex``/``cplex`` are not installed.  The Community Edition
from PyPI (``pip install cplex docplex``) is enough for these instances.
"""

import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.verify import brute_force, check_solution

try:
    import docplex.mp.model  # noqa: F401

    from vrptw.model import build_model, solve

    HAVE_SOLVER = True
except ImportError:  # pragma: no cover
    HAVE_SOLVER = False


@unittest.skipUnless(HAVE_SOLVER, "docplex/cplex not installed")
class TestModel(unittest.TestCase):
    def test_sample_instance_matches_brute_force(self):
        inst = sample_instance()
        sol = solve(inst)
        self.assertIsNotNone(sol)
        self.assertEqual(check_solution(inst, sol.routes), [])
        self.assertAlmostEqual(sol.distance, brute_force(inst).distance, places=6)
        self.assertEqual(sol.distance, 156.2)

    def test_idle_vehicles_cost_nothing_and_come_last(self):
        inst = sample_instance()
        sol = solve(inst)
        self.assertEqual(sol.vehicles_used, 2)
        self.assertEqual(sol.routes[2:], ((), (), ()))
        total = sum(
            inst.distance[a][b] for r in sol.routes if r for a, b in zip((0, *r), (*r, inst.end_depot), strict=True)
        )
        self.assertAlmostEqual(total, sol.distance, places=6)

    def test_relaxed_windows(self):
        inst = relaxed_windows(sample_instance())
        sol = solve(inst)
        self.assertEqual(check_solution(inst, sol.routes), [])
        self.assertAlmostEqual(sol.distance, brute_force(inst).distance, places=6)

    def test_infeasible_instance(self):
        self.assertIsNone(solve(sample_instance().with_vehicles(1)))

    def test_random_instances_match_brute_force(self):
        for seed in range(4):
            inst = random_instance(seed)
            expected = brute_force(inst)
            got = solve(inst)
            with self.subTest(seed=seed):
                if expected is None:
                    self.assertIsNone(got)
                    continue
                self.assertIsNotNone(got)
                self.assertEqual(check_solution(inst, got.routes), [])
                self.assertAlmostEqual(got.distance, expected.distance, places=6)

    def test_symmetry_breaking_does_not_change_the_optimum(self):
        inst = random_instance(7)
        with_sb = solve(inst, symmetry_breaking=True)
        without_sb = solve(inst, symmetry_breaking=False)
        self.assertAlmostEqual(with_sb.distance, without_sb.distance, places=6)

    def test_model_size_omits_forbidden_arcs(self):
        inst = sample_instance()
        built = build_model(inst)
        allowed = sum(inst.arc_allowed(i, j) for i in inst.nodes for j in inst.nodes)
        self.assertEqual(len(built.x), inst.vehicles * allowed)
        self.assertLess(allowed, 7 * 7, "time windows should prune arcs")
        self.assertLess(built.model.number_of_variables, 1000, "fits in the CPLEX Community Edition")


if __name__ == "__main__":
    unittest.main()
