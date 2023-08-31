import logging
from tests.check import check, report_results
from tests.log_settings import setup_logger
import z3

# Verification of GHZ States
logger = setup_logger("ghz.log")
for i in range(2,9):
    logger.info("Checking ghz" + str(i))
    times = check("ghz" + str(i) + ".slq",
                  "ghz",
                  z3.unsat,
                  log_level=logging.ERROR,
                  )
    report_results(logger, times)