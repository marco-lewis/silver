import Process

# Class for representation of programs from Silq
# Should convert JSON into processes
# As advance program, update memory for each command
# Then convert program to proof obligations using the ObligationGenerator
class Program():
    current_time = 0
    quantum_processes = {}
    classical_processes = {}
    
    def __init__(self) -> None:
        pass