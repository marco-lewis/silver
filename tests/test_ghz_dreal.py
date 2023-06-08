import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check, Z3
from tests.log_settings import setup_logger
import z3

# Verification of GHZ States
logger = setup_logger("ghzdreal.log")
for i in range(2,9):
    logger.info("Checking ghz" + str(i))
    avg_setup, avg_solve = check("ghz" + str(i) + ".slq",
                                 "ghz",
                                 DREAL_UNSAT,
                                 log_level=logging.ERROR,
                                 check_store=True,
                                 mode=DREAL,
                                 runs=10)
    logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))