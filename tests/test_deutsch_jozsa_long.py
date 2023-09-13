import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
logger = setup_logger("dj.log")
times = check("dj_fixed5.slq",
            "fixed_dj",
            z3.unsat,
            spq_file=folder+"dj_fixed5.spq",
            log_level=logging.ERROR,
            )
