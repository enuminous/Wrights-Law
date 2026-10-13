import unittest,numpy as np
from emerg001 import run
class TestExperiment(unittest.TestCase):
 def test_repeatable(self):self.assertEqual(run(1,12,40),run(1,12,40))
 def test_modes(self):self.assertEqual([x['mode'] for x in run(2,12,40)],['uncoupled','coupled','adaptive'])
 def test_finite(self):self.assertTrue(all(np.isfinite(x['mean_error']) for x in run(3,12,40)))
if __name__=='__main__':unittest.main()
