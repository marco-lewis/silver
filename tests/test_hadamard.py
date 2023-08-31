import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check
from tests.log_settings import setup_logger
import z3

logger = setup_logger("had.log")
times = check("hadamard5.slq",
                "hadamard",
                z3.unsat,
                )

times = check("hadamard5.slq",
                "hadamard",
                DREAL_UNSAT,
                check_store=True,
                mode=DREAL,
                )


times = check("hadamard5_partial.slq",
                "hadamard",
                z3.unsat,
                )

times = check("hadamard5_partial.slq",
                "hadamard",
                DREAL_UNSAT,
                check_store=True,
                mode=DREAL,
                )

