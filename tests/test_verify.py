import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.data import Instance
from vrptw.verify import brute_force, check_solution, route_distance, route_schedule

OPTIMAL_SAMPLE_DISTANCE = 156.2


class TestRouteSchedule(unittest.TestCase):
    def setUp(self):
        self.inst = sample_instance()

    def test_waits_for_window_to_open(self):
        times = route_schedule(self.inst, (5,))
        # depot -> 5 takes 20.6 but the window opens at 34, then back: 10 service + 20.6
        self.assertEqual(times, [0, 34, 64.6])

    def test_late_arrival_is_infeasible(self):
        self.assertIsNone(route_schedule(self.inst, (1, 2)))

    def test_distance(self):
        self.assertEqual(route_distance(self.inst, ()), 0.0)
        self.assertAlmostEqual(route_distance(self.inst, (5,)), 2 * 20.6)


class TestCheckSolution(unittest.TestCase):
    def setUp(self):
        self.inst = sample_instance()

    def test_feasible(self):
        self.assertEqual(check_solution(self.inst, [(5, 3, 1), (2, 4), (), (), ()]), [])

    def test_detects_violations(self):
        problems = check_solution(self.inst, [(5, 3, 1, 1), (4, 9), (1, 2), (), (), ()])
        joined = "\n".join(problems)
        self.assertIn("6 routes but only 5 vehicles", joined)
        self.assertIn("customer 1 visited 3 times", joined)
        self.assertIn("9 is not a customer", joined)
        self.assertIn("route 2: time windows cannot be met", joined)
        self.assertNotIn("customer 4", joined)

    def test_capacity(self):
        small = Instance(
            1, 20, self.inst.demand, self.inst.ready, self.inst.due, self.inst.service, self.inst.x, self.inst.y
        )
        self.assertIn("route 0: load 45 exceeds capacity 20", check_solution(small, [(4, 5)]))


class TestBruteForce(unittest.TestCase):
    def test_sample_optimum(self):
        inst = sample_instance()
        sol = brute_force(inst)
        self.assertIsNotNone(sol)
        self.assertEqual(sol.distance, OPTIMAL_SAMPLE_DISTANCE)
        self.assertEqual(sol.vehicles_used, 2)
        self.assertEqual(len(sol.routes), inst.vehicles)
        self.assertEqual(check_solution(inst, sol.routes), [])

    def test_relaxed_windows_is_a_cvrp(self):
        inst = relaxed_windows(sample_instance())
        sol = brute_force(inst)
        self.assertEqual(sol.vehicles_used, 1, "capacity 200 fits all 75 units of demand")
        self.assertLess(sol.distance, OPTIMAL_SAMPLE_DISTANCE)
        self.assertEqual(check_solution(inst, sol.routes), [])

    def test_infeasible_when_fleet_too_small(self):
        inst = sample_instance().with_vehicles(1)
        self.assertIsNone(brute_force(inst))

    def test_limit(self):
        with self.assertRaises(ValueError):
            brute_force(random_instance(1, customers=9), max_customers=8)

    def test_random_instances_are_feasible(self):
        for seed in range(3):
            inst = random_instance(seed)
            sol = brute_force(inst)
            if sol is not None:
                self.assertEqual(check_solution(inst, sol.routes), [])


if __name__ == "__main__":
    unittest.main()
