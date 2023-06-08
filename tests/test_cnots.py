import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

logger = setup_logger("ctrl.log")
avg_setup, avg_solve = check("cnot.slq",
                             "cnot",
                             z3.unsat,
                             runs = 10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("ccnot.slq",
                            "ccnot",
                            z3.unsat,
                            runs = 10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("cz.slq",
                               "cz",
                               z3.unsat,
                               runs=10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
