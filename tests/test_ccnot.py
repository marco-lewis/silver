import logging
from tests.check import check
import z3

check("ccnot.slq", "ccnot", z3.unsat, log_level=logging.DEBUG)