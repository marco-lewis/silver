import logging
from tests.check import check, DREAL, Z3
from tests.log_settings import setup_logger
import z3

# Verification of GHZ States
logger = setup_logger("ghz.log")
for i in range(2,9):
    logger.info("Checking ghz" + str(i))
    avg_setup, avg_solve = check("ghz" + str(i) + ".slq", "ghz", z3.unsat, log_level=logging.ERROR, runs=1)
    logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))