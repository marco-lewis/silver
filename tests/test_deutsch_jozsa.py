import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("dj.log")
for i in range(2,9):
    logger.info("Checking fixed_dj" + str(i))
    avg_setup, avg_solve = check("dj_fixed" + str(i) + ".slq", "fixed_dj", z3.unsat, log_level=logging.ERROR, runs=1)
    logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))