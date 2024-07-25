# How to run TLA+

We recommend using the TLA+ Nightly extension for Visual Studio Code to run TLA+.

1. Focus on a tla file
2. Execute this command in the Visual Studio Code Command Palette.
```
>TLA+:Check model with TLC
```
3. Additional options pass to TLC

to speed up:
```
-workers 8
```

to dump all states:
```
-dump dump.txt
```