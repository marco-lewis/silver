# SilSpeq

A specification language for verifying Silq programs.

## File Navigation

`examples/` - contains examples of specifications written in SilSpeq

`SilSpeq.lark` - grammar of SilSpeq (based on grammars presented in [Lark](https://github.com/lark-parser/lark)).

`SilSpeqParser.py` - parser for SilSpeq. The transformer can be changed to one of the visitors available.

`SilSpeqZ3FlagVisitor.py` - visitor that checks for flag options.

`SilSpeqZ3Interpreter.py` - visitor that converts SilSpeq into Z3 program obligations.

`example.py` - example run (used for checking interpreter).

## Links
Silq - https://github.com/eth-sri/silq
