"""
Universal setup for Marlin
"""
import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))

from babysnark import random_fp, G
from util import nearestPowerOfTwo


class UniversalSetup:
    def __init__(self, max_constraints, max_variables, max_non_zero):
        self.max_variables = max_variables
        self.max_constraints = max_constraints
        self.max_non_zero = max_non_zero

        self.max_degree = nearestPowerOfTwo(
            max(max_constraints, max_variables, max_non_zero)
        )
        # Find the max degree of the polycommit scheme we
        # want to support
        tau = random_fp()
        self.CRS = [G * (tau ** i) for i in range(self.max_degree + 1)]
