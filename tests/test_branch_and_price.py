import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.verify import brute_force, check_solution

try:
    import cplex  # noqa: F401

    from vrptw.branch_and_price import branch_and_price

    HAVE_SOLVER = True
except ImportError:  # pragma: no cover
    HAVE_SOLVER = False


@unittest.skipUnless(HAVE_SOLVER, "cplex not installed")
class TestBranchAndPrice(unittest.TestCase):
    def test_sample(self):
        inst = sample_instance()
        result = branch_and_price(inst)
        self.assertEqual(result.status, "optimal")
        self.assertEqual(result.solution.distance, 156.2)
        self.assertEqual(result.solution.vehicles_used, 2)
        self.assertEqual(check_solution(inst, result.solution.routes), [])
        self.assertGreater(result.columns, inst.n)
        self.assertLessEqual(result.root_bound, 156.2 + 1e-6)

    def test_relaxed_windows(self):
        inst = relaxed_windows(sample_instance())
        result = branch_and_price(inst)
        self.assertEqual(check_solution(inst, result.solution.routes), [])
        self.assertAlmostEqual(result.solution.distance, brute_force(inst).distance, places=6)

    def test_infeasible(self):
        result = branch_and_price(sample_instance().with_vehicles(1))
        self.assertIsNone(result.solution)
        self.assertEqual(result.status, "infeasible")

    def test_random_instances_match_brute_force(self):
        for seed in range(8):
            inst = random_instance(seed, customers=7, vehicles=4, capacity=45)
            expected = brute_force(inst)
            result = branch_and_price(inst)
            with self.subTest(seed=seed):
                if expected is None:
                    self.assertIsNone(result.solution)
                    continue
                self.assertEqual(result.status, "optimal")
                self.assertEqual(check_solution(inst, result.solution.routes), [])
                self.assertAlmostEqual(result.solution.distance, expected.distance, places=6)

    def test_matches_the_mip_on_a_larger_instance(self):
        from vrptw.model import solve

        inst = random_instance(11, customers=12, vehicles=5, capacity=60)
        mip = solve(inst, formulation="two-index")
        result = branch_and_price(inst)
        self.assertEqual(result.status, "optimal")
        self.assertEqual(check_solution(inst, result.solution.routes), [])
        self.assertAlmostEqual(result.solution.distance, mip.distance, places=6)

    def test_time_limit_is_honoured(self):
        inst = random_instance(4, customers=7, vehicles=4, capacity=45)
        result = branch_and_price(inst, time_limit=0.0)
        self.assertIn(result.status, ("time_limit", "optimal"))
        if result.solution is not None:
            self.assertEqual(check_solution(inst, result.solution.routes), [])
            self.assertLessEqual(result.lower_bound, result.upper_bound + 1e-6)


if __name__ == "__main__":
    unittest.main()
