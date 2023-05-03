import logging
from tests.check import check
import z3

check("cnot.slq", "cnot", z3.unsat)
check("ccnot.slq", "ccnot", z3.unsat)