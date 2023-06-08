import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import folder, check
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("djdreal.log")
for i in range(2,9):
    logger.info("Checking fixed_dj" + str(i))
    logger.info("Checking constant")
    avg_setupC, avg_solveC = check("dj_fixed" + str(i) + ".slq",
                                "fixed_dj",
                                DREAL_UNSAT,
                                spq_file=folder+"dj_fixed" + str(i) + "const.spq",
                                check_store=True,
                                log_level=logging.ERROR,
                                mode=DREAL,
                                runs=10
                                )
    logger.info("(Constant) Setup average: %s, Run average: %s", str(avg_setupC), str(avg_solveC))
    logger.info("Checking balanced")
    avg_setupB, avg_solveB = check("dj_fixed" + str(i) + ".slq",
                                 "fixed_dj",
                                 DREAL_UNSAT,
                                 spq_file=folder+"dj_fixed" + str(i) + "bal.spq",
                                 check_store=True,
                                 log_level=logging.ERROR,
                                 mode=DREAL,
                                 runs=10)
    logger.info("(Balanced) Setup average: %s, Run average: %s", str(avg_setupB), str(avg_solveB))
    avg_setup = avg_setupC
    avg_solve = (avg_solveB + avg_solveC)/2
    logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))