import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Grover's Algorithm
logger = setup_logger("grover.log")
# 1 Call
# 2 qubits - uses certainty
logger.info("Checking grover_fixed2")
times = check("grover_fixed2.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR, runs=10)

logger.info("Checking grover_fixed2 (alt)")
times = check("grover_fixed2.slq", "grover_fixed", z3.unsat, spq_file=folder + "grover_fixed2alt.spq", log_level=logging.ERROR, runs=10)

# times = check("grover_partial3.slq", "grover_partial", z3.unsat, runs=10)


# 2 Calls
logger.info("Checking grover_fixed3")
times = check("grover_fixed3.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR)

# 3 Calls - 4-14?
# logger.info("Checking grover_fixed4")
# times = check("grover_fixed4.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR,)

# logger.info("Checking grover_fixed5")
# times = check("grover_fixed5.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR,)

# logger.info("Checking grover_fixed6")
# times = check("grover_fixed6.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR,)

# logger.info("Checking grover_fixed7")
# times = check("grover_fixed7.slq", "grover_fixed", z3.unsat, log_level=logging.ERROR,)
