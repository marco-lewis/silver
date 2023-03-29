import logging
from tests.check import check
import z3

# Verification of GHZ States
check("ghz2.slq", "ghz", z3.unsat, log_level=logging.DEBUG)
check("ghz3.slq", "ghz", z3.unsat)
check("ghz4.slq", "ghz", z3.unsat)
check("ghz5.slq", "ghz", z3.unsat)
check("ghz6.slq", "ghz", z3.unsat)
check("ghz7.slq", "ghz", z3.unsat)
check("ghz8.slq", "ghz", z3.unsat)