# SilVer [In Development/Unstable]

Development of the SilVer tool for verifying Silq programs using the Z3 SMT solver.

## File Navigation

`Silq Programs/` - folder containing a number of programs written in Silq and respective SilSpeq files. Also, contains `.ast` where AST of program files in json format

`silspeq/` - SilSpeq submodule for specifying behaviour

`silver/` - contains files for SilVer

`tests/` - contains tests for checking SilVer functionality

### Misc Files

`get_ast(_silq_folder).sh` - makes calls to Silq to generate json and store them in tests. Requires Silq binary from [this Silq fork](https://github.com/marco-lewis/silq/tree/ast-file).

## Current Workflow

1. Add your Silq file to `Silq_Programs`

2. Create a Python file that creates a `silver = SilVer()` object and run:

    `silver.verify_func(<silq-file-location>,<function-to-verify>)`
    
    On the first run a spq file will be created which can be used to specify behaviour using SilSpeq. When ran again, SilVer will verify the function specified.
