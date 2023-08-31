import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check, report_results
from tests.log_settings import setup_logger
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("bvdreal.log")
for i in range(2,9):
    logger.info("Checking bv_fixed" + str(i))
    times = check("bv_fixed" + str(i) + ".slq",
                "fixed_bv",
                DREAL_UNSAT,
                check_store=True,
                log_level=logging.ERROR,
                mode=DREAL,
                )
    report_results(logger, times)