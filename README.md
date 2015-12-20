# ATS playground

This repository contains various ideas and proofs of concept
techniques implemented in the ATS2 programming language.

[More info about ATS2](http://www.ats-lang.org/)

## lines example

"lines" is a simple software rasterization benchmark, please see:

https://github.com/alekseysidorov/playground/tree/master/swift_vs_rust/raster

for details. To build the ATS version, please use:

```
make -f Makefile_lines`
```

To run the program, please use:

```
./lines
```

The program can also output a PPM file prior to exiting. If this is
what you want, please comment out a call to `pixmap_save_ppm` in the
`main0` function).

--Artyom Shalkhakov

