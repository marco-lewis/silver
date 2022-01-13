from enum import Enum
class MeasureOptions(Enum):
    HIGH_PROB = 1
    CERTAINTY = 2
    SPECIFIC_VALUE = 3

MEASURE_OPTION = "MEASURE_OPTION"
HIGH_PROB = MeasureOptions.HIGH_PROB
CERTAINTY = MeasureOptions.CERTAINTY
SPECIFIC_VALUE = MeasureOptions.SPECIFIC_VALUE