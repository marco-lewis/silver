import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check, report_results
from tests.log_settings import setup_logger
import z3

logger = setup_logger("had.log")
times = check("hadamard5.slq",
                "hadamard",
                z3.unsat,
                )
report_results(logger, times)
times = check("hadamard5.slq",
                "hadamard",
                DREAL_UNSAT,
                check_store=True,
                mode=DREAL,
                )
report_results(logger, times)

times = check("hadamard5_partial.slq",
                "hadamard",
                z3.unsat,
                )
report_results(logger, times)
times = check("hadamard5_partial.slq",
                "hadamard",
                DREAL_UNSAT,
                check_store=True,
                mode=DREAL,
                )
report_results(logger, times)
