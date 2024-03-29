import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Bernstein-Vazirani for n-qubits
logger = setup_logger("bv.log")
for i in range(2,9):
    times = check("bv_fixed" + str(i) + ".slq",
                    "fixed_bv",
                    z3.unsat,
                    log_level=logging.ERROR,
                    )