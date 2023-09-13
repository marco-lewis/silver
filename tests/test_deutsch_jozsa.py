import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("dj.log")
for i in range(2,6):
    times = check("dj_fixed" + str(i) + ".slq",
                "fixed_dj",
                z3.unsat,
                spq_file=folder+"dj_fixed" + str(i) + ".spq",
                log_level=logging.ERROR,
                timeout=20*60*1000
                )
