import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
setup_logger("bv.log")
check("bv_fixed2.slq", "fixed_bv", z3.unsat)
check("bv_fixed5.slq", "fixed_bv", z3.unsat)
check("bv_fixed10.slq", "fixed_bv", z3.unsat, check_store=True)
check("bv_fixed12.slq", "fixed_bv", z3.unsat)