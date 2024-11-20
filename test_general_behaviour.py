from silver.silver.SilVer import SilVer

import logging

silver = SilVer()
file_name = "examples/Silq_Programs/dj_general"
silver.verify_func(file_name + ".slq", "dj", log_level=logging.INFO, spq_file = file_name + ".spq", hyperparameters={'n': 2})