import logging
from tests.check import check, report_results
from tests.log_settings import setup_logger
import z3

logger = setup_logger("ctrl.log")
times = check("cnot.slq",
                "cnot",
                z3.unsat,
                )
report_results(logger, times)
times = check("ccnot.slq",
                "ccnot",
                z3.unsat,
                )
report_results(logger, times)
times = check("cz.slq",
                "cz",
                z3.unsat,
                )
report_results(logger, times)