from tests.check import check
import z3

# Basic checks that SilVer compiles correctly
check("test_singlevar.json", "main", z3.sat)
check("test_unitary.json", "main", z3.sat)
check("uint.json", "uint_test", z3.sat)
check("types.json", "main", z3.sat)