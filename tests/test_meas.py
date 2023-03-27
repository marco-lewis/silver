import logging
from tests.check import check
import z3

check("measurement.slq", "rand", z3.unsat, log_level = logging.INFO)
# check("measurement.slq", "cert", z3.unsat)
# check("measurement.slq", "rand", z3.unsat)
# check("measurement.slq", "rand", z3.unsat)
