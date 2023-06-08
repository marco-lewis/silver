import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check
from tests.log_settings import setup_logger
import z3

logger = setup_logger("had.log")
avg_setup, avg_solve = check("hadamard5.slq",
                               "hadamard",
                               z3.unsat,
                               runs=10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("hadamard5.slq",
                               "hadamard",
                               DREAL_UNSAT,
                               check_store=True,
                               mode=DREAL,
                               runs=10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
