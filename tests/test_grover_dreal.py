import logging
from silver.silver.utils import DREAL, DREAL_UNSAT
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Grover's Algorithm
logger = setup_logger("groverdreal.log")
# 1 Call
# 2 qubits - uses certainty

times = check("grover_fixed2.slq",
                "grover_fixed",
                DREAL_UNSAT,
                log_level=logging.ERROR,
                mode=DREAL,
                check_store=True)


# 2 Calls

times = check("grover_fixed3.slq",
                "grover_fixed",
                DREAL_UNSAT,
                log_level=logging.ERROR,
                mode=DREAL,
                check_store=True)
