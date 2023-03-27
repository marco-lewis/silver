import logging
from tests.check import check
import z3

# Verification of Simon
# simon<n> - Simon for n-qubits
check("simon2.slq", "simon", z3.unsat)