import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

# Verification of GHZ States
logger = setup_logger("ghz.log")
for i in range(2,9):
    times = check("ghz" + str(i) + ".slq",
                  "ghz",
                  z3.unsat,
                  log_level=logging.ERROR,
                  )