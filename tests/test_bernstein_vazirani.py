from tests.check import check
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
check("bv_fixed2.json", "fixed_bv", z3.unsat)