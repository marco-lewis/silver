import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("bv.log")
for i in range(2,9):
    logger.info("Checking bv_fixed" + str(i))
    avg_setup, avg_solve = check("bv_fixed" + str(i) + ".slq", "fixed_bv", z3.unsat, log_level=logging.ERROR, runs=10)
    logger.info("Setup average: %ss, Run average: %ss", str(avg_setup), str(avg_solve))