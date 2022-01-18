# Future Example Process
Say user file looks like this:

```
dict
|   program.slq
|   ...
```

When SilVer is run, SilVer should first call `silq [FILE] --ast-dump` (need silq on PATH) and store the AST of program.slq in a hidden folder .ast:

```
dir
|   program.slq
|
└───.ast
|   | program.json
|
|   ...
```

If a SilSpeq file of program does not exist, a new one should be created in the main directory:

```
dir
|   program.slq
|   program.spq
|
└───.ast
|   | program.json
|
|   ...
```

If one is already there, the proof obligations and the verification should take place as normal.

(Could also add hashes to check between current program AST and the one stored in .ast. Perhaps a .hash folder?)