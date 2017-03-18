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

## `shuntingyard.dats`

Shunting yard algorithm implementation. Provides a math formula
calculator for testing. All memory allocation is managed manually.

## `loadtga.dats`

A command-line utility to load an image file in TGA format and convert
it to a PPM file. Using pervasive manual memory allocation, the style
is very similar to what you would use in C.

## `starray.dats`

A static array with shared (non-linear) pointers taken out from
it. Useful if you want to implement a system where some named
resources can be allocated and then referred to by user.

## `tuple.dats`

An attempt to provide Ur/Web-style tuples for ATS.

## `binheap.dats`

A safe binary heap implementation. Converted from C to ATS.

## `exptmp.dats`

A C++ expression template example ported to ATS.

## `fundigraph`

Functional implementation of a directed graph (internally represented
as adjacency list).

## `mathlib`

Figuring out how to implement low-dimensional vectors and matrices in
ATS, with application to computer graphics.

--Artyom Shalkhakov

