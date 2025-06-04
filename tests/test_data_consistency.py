import os
import re
import unittest


class TestDataConsistency(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        dat_path = os.path.join(os.path.dirname(__file__), '..', 'VRPTW.dat')
        with open(dat_path, 'r') as f:
            cls.data = f.read()

    def extract_array(self, name):
        pattern = re.compile(r"%s\s*=\s*#\[(.*?)\]#;" % re.escape(name), re.S)
        match = pattern.search(self.data)
        self.assertIsNotNone(match, f"{name} array not found")
        body = match.group(1)
        values = re.findall(r":\s*([0-9]+)", body)
        return [int(v) for v in values]

    def test_demand_length(self):
        m = re.search(r"CustomersNumber\s*=\s*(\d+);", self.data)
        self.assertIsNotNone(m, "CustomersNumber not found")
        customers = int(m.group(1))
        demand = self.extract_array('Demand')
        self.assertEqual(len(demand), customers)

    def test_other_arrays_length(self):
        m = re.search(r"CustomersNumber\s*=\s*(\d+);", self.data)
        self.assertIsNotNone(m, "CustomersNumber not found")
        customers = int(m.group(1))
        for arr in ['ServiceTime', 'XCoord', 'YCoord', 'LBTW', 'UBTW']:
            values = self.extract_array(arr)
            self.assertEqual(len(values), customers + 2,
                             f"{arr} length should be CustomersNumber + 2")


if __name__ == '__main__':
    unittest.main()
