import logging
from tests.check import check
import z3

check("measurement.slq", "rand", z3.unsat)
check("measurement.slq", "whp", z3.unsat)
check("measurement.slq", "atval", z3.unsat)
# check("measurement.slq", "whpatval", z3.unsat)
# check("measurement.slq", "cert", z3.unsat, log_level=logging.DEBUG)