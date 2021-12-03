class Command():
    def __init__(self) -> None:
        pass
    

# Stores the operation, variables (with renaming) and what controls are on the operation
class QuantumCommand():
    controls = None
    operation = None
    
    in_vars = None
    out_vars = None
    
    def __init__(self) -> None:
        pass
    
# Stores operation to be performed, variables used and where they are being assigned to
class ClassicalCommand():
    command = None
    
    in_vars = None
    out_vars = None
    
    def __init__(self) -> None:
        pass