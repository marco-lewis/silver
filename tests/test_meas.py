import logging
from tests.check import check
import z3

check("measurement.slq", "rand", z3.unsat)
check("measurement.slq", "whp", z3.unsat)
check("measurement.slq", "atval", z3.unsat)
# BUG: returns false on cos/sin values; use dReal?
# check("measurement.slq", "whpatval", z3.unsat, log_level=logging.DEBUG)
# BUG: Python/Z3 faces a segmentation fault
# check("measurement.slq", "cert", z3.unsat, log_level=logging.DEBUG)