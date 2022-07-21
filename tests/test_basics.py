from tests.check import check
import z3

# Basic checks that SilVer compiles correctly
# TODO: Create missing files
check("test_singlevar.slq", "main", z3.sat)
check("test_unitary.slq", "main", z3.sat)
check("uint.slq", "uint_test", z3.sat)
check("types.slq", "main", z3.sat)