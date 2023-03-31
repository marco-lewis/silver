import logging
from tests.check import check
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
check("bv_fixed2.slq", "fixed_bv", z3.unsat)
check("bv_fixed3.slq", "fixed_bv", z3.unsat)
check("bv_fixed4.slq", "fixed_bv", z3.unsat)
check("bv_fixed5.slq", "fixed_bv", z3.unsat)
# # Takes ~45s for 6 qubit case
check("bv_fixed6.slq", "fixed_bv", z3.unsat)
check("bv_fixed7.slq", "fixed_bv", z3.unsat)
check("bv_fixed8.slq", "fixed_bv", z3.unsat)