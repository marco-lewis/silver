import logging
from tests.check import check
import z3

# Verification of GHZ States
check("ctrl1.slq", "ctrl1", z3.unsat, log_level=logging.DEBUG)