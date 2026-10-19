import tempfile
import unittest
from pathlib import Path

from tests.helpers import FIXTURES, SAMPLE_DAT, sample_instance
from vrptw.data import (
    Instance,
    format_dat,
    instance_from_dat_values,
    parse_dat,
    parse_solomon,
    read_dat,
    read_solomon,
    truncated_distance,
    write_dat,
)


class TestSampleData(unittest.TestCase):
    def setUp(self):
        self.inst = sample_instance()

    def test_dimensions(self):
        self.assertEqual(self.inst.n, 5)
        self.assertEqual(self.inst.vehicles, 5)
        self.assertEqual(self.inst.capacity, 200)
        self.assertEqual(len(self.inst.demand), 7)
        self.assertEqual(list(self.inst.customers), [1, 2, 3, 4, 5])
        self.assertEqual(self.inst.end_depot, 6)

    def test_sample_is_consistent(self):
        self.assertEqual(self.inst.validate(), [])

    def test_end_depot_is_a_copy_of_the_depot(self):
        i = self.inst
        self.assertEqual((i.x[0], i.y[0]), (i.x[6], i.y[6]))
        self.assertEqual(i.service[6], 0)
        self.assertEqual(i.demand[6], 0)
        self.assertEqual((i.ready[0], i.due[0]), (i.ready[6], i.due[6]))

    def test_sample_matches_solomon_r101(self):
        """The sample is the depot plus the first five customers of R101."""
        r101 = read_solomon(FIXTURES / "R101_head.txt", customers=5, vehicles=5)
        self.assertEqual(r101, self.inst)

    def test_every_dat_parameter_is_declared_in_the_model(self):
        import re

        declared = set(
            re.findall(
                r"^\s*(?:int|float)\s+(\w+)(?:\[[^\]]*\])?\s*=\s*\.\.\.;",
                (SAMPLE_DAT.parent / "VRPTW.mod").read_text(),
                re.M,
            )
        )
        provided = set(parse_dat(SAMPLE_DAT.read_text()))
        self.assertEqual(declared, provided)


class TestDistances(unittest.TestCase):
    def test_truncation_to_one_decimal(self):
        self.assertEqual(truncated_distance(0, 0, 3, 4), 5.0)
        self.assertEqual(truncated_distance(35, 35, 41, 49), 15.2)  # sqrt(232) = 15.231...
        self.assertEqual(truncated_distance(0, 0, 1, 1), 1.4)  # sqrt(2) = 1.414... truncated, not rounded

    def test_matrices(self):
        inst = sample_instance()
        for i in inst.nodes:
            self.assertEqual(inst.distance[i][i], 0.0)
            self.assertEqual(inst.time[i][i], 0.0)
            for j in inst.nodes:
                self.assertEqual(inst.distance[i][j], inst.distance[j][i])
                if i != j:
                    self.assertEqual(inst.time[i][j], inst.distance[i][j] + inst.service[i])
        self.assertEqual(inst.distance[0][1], 15.2)
        self.assertEqual(inst.time[1][0], 25.2)  # 10 service + 15.2 travel
        self.assertEqual(inst.time[0][6], 0.0)  # depot to its copy

    def test_big_m_and_allowed_arcs(self):
        inst = sample_instance()
        self.assertEqual(inst.big_m(0, 6), 230)
        self.assertEqual(inst.big_m(1, 2), 171 + inst.time[1][2] - 50)  # 171 + 42.5 - 50
        self.assertEqual(inst.big_m(2, 1), 0.0, "arc 2 -> 1 can never be late: 60 + 42.5 < 161")
        self.assertFalse(inst.arc_allowed(1, 1))
        self.assertFalse(inst.arc_allowed(3, 0), "nothing may enter the start depot")
        self.assertFalse(inst.arc_allowed(6, 3), "nothing may leave the end depot")
        self.assertTrue(inst.arc_allowed(0, 6), "idle vehicles go straight to the end depot")
        # customer 1 opens at 161, customer 2 closes at 60: 1 -> 2 is impossible
        self.assertFalse(inst.arc_allowed(1, 2))
        self.assertTrue(inst.arc_allowed(2, 1))


class TestInstanceValidation(unittest.TestCase):
    def test_detects_misplaced_end_depot(self):
        """Regression test for the original sample, whose node 6 was a customer."""
        inst = sample_instance()
        broken = Instance(
            vehicles=inst.vehicles,
            capacity=inst.capacity,
            demand=inst.demand,
            ready=inst.ready,
            due=inst.due,
            service=(*inst.service[:6], 10),
            x=(*inst.x[:6], 65),
            y=(*inst.y[:6], 20),
        )
        problems = broken.validate()
        self.assertTrue(any("coordinates" in p for p in problems))
        self.assertTrue(any("service time" in p for p in problems))

    def test_detects_unservable_customer_and_bad_window(self):
        inst = sample_instance()
        due = list(inst.due)
        due[3] = 5  # customer 3 cannot be reached by time 5
        bad = Instance(inst.vehicles, inst.capacity, inst.demand, inst.ready, tuple(due), inst.service, inst.x, inst.y)
        problems = bad.validate()
        self.assertTrue(any("customer 3" in p for p in problems))
        self.assertTrue(any("node 3: time window" in p for p in problems))

    def test_detects_oversized_demand(self):
        inst = sample_instance()
        demand = list(inst.demand)
        demand[2] = 201
        bad = Instance(inst.vehicles, inst.capacity, tuple(demand), inst.ready, inst.due, inst.service, inst.x, inst.y)
        self.assertIn("customer 2: demand exceeds vehicle capacity", bad.validate())

    def test_rejects_inconsistent_lengths(self):
        with self.assertRaises(ValueError):
            Instance(1, 10, (0, 1), (0, 0, 0), (9, 9, 9), (0, 0, 0), (0, 1, 0), (0, 1, 0))


class TestDatFormat(unittest.TestCase):
    def test_parse_scalars_arrays_and_comments(self):
        values = parse_dat("// c\n v = 2; /* multi\nline */ CustomersNumber=1;\nDemand = #[ 1: 4 ]#;")
        self.assertEqual(values, {"v": 2, "CustomersNumber": 1, "Demand": {1: 4.0}})

    def test_missing_parameter(self):
        with self.assertRaisesRegex(ValueError, "missing data: .*Capacity"):
            instance_from_dat_values({"v": 1, "CustomersNumber": 1})

    def test_wrong_index_range(self):
        values = parse_dat(SAMPLE_DAT.read_text())
        values["Demand"] = {0: 0, **values["Demand"]}  # demand must be indexed 1..n
        with self.assertRaisesRegex(ValueError, "Demand: expected indices 1..5"):
            instance_from_dat_values(values)

    def test_round_trip(self):
        inst = sample_instance()
        text = format_dat(inst)
        again = instance_from_dat_values(parse_dat(text), name=inst.name)
        self.assertEqual(again, inst)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "copy.dat"
            write_dat(inst, path)
            self.assertEqual(read_dat(path).distance, inst.distance)


class TestSolomonFormat(unittest.TestCase):
    def test_full_file(self):
        inst = read_solomon(FIXTURES / "R101_head.txt")
        self.assertEqual(inst.name, "R101")
        self.assertEqual(inst.n, 7)
        self.assertEqual(inst.vehicles, 25)
        self.assertEqual(inst.capacity, 200)
        self.assertEqual(inst.demand[7], 5)
        self.assertEqual((inst.ready[7], inst.due[7]), (81, 91))
        self.assertEqual((inst.x[8], inst.y[8], inst.demand[8], inst.service[8]), (35, 35, 0, 0))
        self.assertEqual(inst.validate(), [])

    def test_subset_and_fleet_override(self):
        inst = read_solomon(FIXTURES / "R101_head.txt", customers=2, vehicles=1)
        self.assertEqual(inst.n, 2)
        self.assertEqual(inst.vehicles, 1)
        self.assertEqual(inst.end_depot, 3)

    def test_malformed(self):
        with self.assertRaises(ValueError):
            parse_solomon("R1\n\nVEHICLE\n1 2\n\n1 2 3\n")
        with self.assertRaises(ValueError):
            parse_solomon("")


if __name__ == "__main__":
    unittest.main()
