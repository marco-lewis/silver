import logging
from tests.check import check
from tests.log_settings import setup_logger
import z3

logger = setup_logger("bv.log")
times = check("setup.slq",
                "main",
                z3.unsat,
                )
