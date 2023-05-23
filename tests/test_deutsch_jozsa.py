import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
setup_logger("dj.log")
check("dj_fixed2.slq", "fixed_dj", z3.unsat)
check("dj_fixed5.slq", "fixed_dj", z3.unsat)
check("dj_fixed10.slq", "fixed_dj", z3.unsat)
check("dj_fixed12.slq", "fixed_dj", z3.unsat)