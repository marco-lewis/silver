import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

# Verification of GHZ States
setup_logger("ghz.log")
check("ghz2.slq", "ghz", z3.unsat)
check("ghz5.slq", "ghz", z3.unsat)
check("ghz10.slq", "ghz", z3.unsat,check_store=True)
check("ghz12.slq", "ghz", z3.unsat)