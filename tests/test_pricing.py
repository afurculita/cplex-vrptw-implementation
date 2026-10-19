import unittest

from tests.helpers import random_instance, sample_instance
from vrptw.pricing import price
from vrptw.verify import route_distance, route_schedule


def route_feasible(inst, route):
    return route_schedule(inst, route) is not None and sum(inst.demand[c] for c in route) <= inst.capacity


class TestPricing(unittest.TestCase):
    def test_no_duals_means_no_negative_routes(self):
        inst = sample_instance()
        self.assertEqual(price(inst, {c: 0.0 for c in inst.customers}, 0.0), [])

    def test_routes_are_feasible_and_reduced_costs_are_right(self):
        inst = sample_instance()
        duals = {c: 60.0 for c in inst.customers}
        found = price(inst, duals, -5.0, max_routes=50)
        self.assertTrue(found)
        for reduced, route in found:
            self.assertTrue(route_feasible(inst, route))
            self.assertEqual(len(set(route)), len(route), "routes are elementary")
            expected = route_distance(inst, route) - sum(duals[c] for c in route) + 5.0
            self.assertAlmostEqual(reduced, expected, places=6)
            self.assertLess(reduced, 0)
        costs = [c for c, _ in found]
        self.assertEqual(costs, sorted(costs), "most negative reduced cost first")

    def test_finds_the_best_route_exactly(self):
        """Compare with an exhaustive enumeration of all feasible routes."""
        from itertools import permutations

        inst = random_instance(2, customers=6, vehicles=3, capacity=40)
        duals = {c: 15.0 + c for c in inst.customers}
        best_cost = 0.0
        for size in range(1, inst.n + 1):
            for route in permutations(inst.customers, size):
                if route_feasible(inst, route):
                    best_cost = min(best_cost, route_distance(inst, route) - sum(duals[c] for c in route))
        found = price(inst, duals, 0.0, max_routes=1)
        self.assertTrue(found)
        self.assertAlmostEqual(found[0][0], best_cost, places=6)

    def test_forbidden_arcs_are_respected(self):
        inst = sample_instance()
        duals = {c: 60.0 for c in inst.customers}
        forbidden = frozenset({(0, 5), (5, 3)})
        for _, route in price(inst, duals, 0.0, forbidden=forbidden, max_routes=50):
            nodes = (0, *route, inst.end_depot)
            self.assertFalse(set(zip(nodes, nodes[1:], strict=False)) & forbidden)


if __name__ == "__main__":
    unittest.main()
