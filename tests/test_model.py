"""End-to-end tests of the formulations, solved with CPLEX through docplex.

Skipped when ``docplex``/``cplex`` are not installed.  The Community Edition
from PyPI (``pip install cplex docplex``) is enough for these instances.
"""

import itertools
import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.verify import brute_force, check_solution

try:
    import docplex.mp.model  # noqa: F401

    from vrptw.model import build_model, solve

    HAVE_SOLVER = True
except ImportError:  # pragma: no cover
    HAVE_SOLVER = False

FORMULATIONS = ("three-index", "two-index")


@unittest.skipUnless(HAVE_SOLVER, "docplex/cplex not installed")
class TestModel(unittest.TestCase):
    def test_sample_instance_matches_brute_force(self):
        inst = sample_instance()
        for formulation in FORMULATIONS:
            with self.subTest(formulation=formulation):
                sol = solve(inst, formulation=formulation)
                self.assertIsNotNone(sol)
                self.assertEqual(check_solution(inst, sol.routes), [])
                self.assertEqual(sol.distance, 156.2)
                self.assertEqual(sol.vehicles_used, 2)
                self.assertEqual(sol.routes[2:], ((), (), ()), "idle vehicles come last")

    def test_relaxed_windows(self):
        inst = relaxed_windows(sample_instance())
        expected = brute_force(inst).distance
        for formulation in FORMULATIONS:
            with self.subTest(formulation=formulation):
                sol = solve(inst, formulation=formulation)
                self.assertEqual(check_solution(inst, sol.routes), [])
                self.assertAlmostEqual(sol.distance, expected, places=6)

    def test_infeasible_instance(self):
        for formulation in FORMULATIONS:
            self.assertIsNone(solve(sample_instance().with_vehicles(1), formulation=formulation))

    def test_random_instances_match_brute_force(self):
        for seed, formulation in itertools.product(range(4), FORMULATIONS):
            inst = random_instance(seed)
            expected = brute_force(inst)
            got = solve(inst, formulation=formulation)
            with self.subTest(seed=seed, formulation=formulation):
                if expected is None:
                    self.assertIsNone(got)
                    continue
                self.assertIsNotNone(got)
                self.assertEqual(check_solution(inst, got.routes), [])
                self.assertAlmostEqual(got.distance, expected.distance, places=6)

    def test_lexicographic_objective(self):
        # On this instance the shortest solution needs 3 vehicles (136.2) while
        # 2 vehicles suffice at a longer distance (151.6), so the objectives differ.
        inst = random_instance(1, customers=7, vehicles=4, capacity=45)
        expected = brute_force(inst, objective="lex")
        self.assertEqual((expected.vehicles_used, expected.distance), (2, 151.6))
        self.assertEqual((brute_force(inst).vehicles_used, brute_force(inst).distance), (3, 136.2))
        for formulation in FORMULATIONS:
            with self.subTest(formulation=formulation):
                got = solve(inst, formulation=formulation, objective="lex")
                self.assertEqual(check_solution(inst, got.routes), [])
                self.assertEqual((got.vehicles_used, got.distance), (2, 151.6))
                shortest = solve(inst, formulation=formulation, objective="distance")
                self.assertEqual((shortest.vehicles_used, shortest.distance), (3, 136.2))

    def test_options_do_not_change_the_optimum(self):
        inst = random_instance(7)
        expected = brute_force(inst).distance
        for formulation in FORMULATIONS:
            for options in (
                dict(symmetry_breaking=False),
                dict(preprocess=False),
                dict(warm_start=False),
                dict(capacity_cut=False),
                dict(preprocess=False, warm_start=False, capacity_cut=False, symmetry_breaking=False),
            ):
                with self.subTest(formulation=formulation, **options):
                    sol = solve(inst, formulation=formulation, **options)
                    self.assertAlmostEqual(sol.distance, expected, places=6)

    def test_model_sizes(self):
        inst = sample_instance()
        three = build_model(inst, "three-index")
        two = build_model(inst, "two-index")
        allowed = sum(inst.arc_allowed(i, j) for i in inst.nodes for j in inst.nodes)
        self.assertEqual(len(three.x), inst.vehicles * allowed)
        self.assertEqual(len(two.x), allowed - 1, "the two-index model has no idle 0 -> n+1 arc")
        self.assertLess(allowed, 7 * 7, "time windows should prune arcs")
        self.assertLess(two.model.number_of_variables, three.model.number_of_variables / 3)
        self.assertLess(three.model.number_of_variables, 1000, "fits in the CPLEX Community Edition")

    def test_time_limit_and_gap_are_accepted(self):
        sol = solve(sample_instance(), time_limit=10, mip_gap=0.0)
        self.assertEqual(sol.distance, 156.2)


if __name__ == "__main__":
    unittest.main()
