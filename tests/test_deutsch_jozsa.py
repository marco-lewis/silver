import logging
from tests.check import check, folder, report_results
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("dj.log")
for i in range(2,9):
    logger.info("Checking fixed_dj" + str(i))
    logger.info("Checking constant")
    times = check("dj_fixed" + str(i) + ".slq",
                "fixed_dj",
                z3.unsat,
                spq_file=folder+"dj_fixed" + str(i) + ".spq",
                log_level=logging.ERROR,
                )
    report_results(logger, times)