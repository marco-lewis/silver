from tests.check import check
import z3

# Verification of Bernstein-Vazirani
# bv_fixed<n> - Deutsch-Jozsa for n-qubits
check("bv_fixed2.json", "fixed_bv", z3.unsat)
check("bv_fixed3.json", "fixed_bv", z3.unsat)
check("bv_fixed4.json", "fixed_bv", z3.unsat)
check("bv_fixed5.json", "fixed_bv", z3.unsat)