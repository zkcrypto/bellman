# BLAKE2 AVX2 implementations

This is **experimental** code implementing [BLAKE2](https://blake2.net/) using the AVX2 instruction set present in the Intel [Haswell](https://en.wikipedia.org/wiki/Haswell_%28microarchitecture%29) and later microarchitectures.

It currently implements BLAKE2b, BLAKE2bp, and BLAKE2sp using 3 similar but slightly different approaches: one lets the compiler choose how to permute the message, another one does it manually, and the final one uses the gather instructions introduced with AVX2. Current recorded speeds for long messages are:

 - 3.19 cycles per byte on Haswell for BLAKE2b;
 - 1.37 cycles per byte on Haswell for BLAKE2bp;
 - 1.39 cycles per byte on Haswell for BLAKE2sp.

 - 3.08 cycles per byte on Skylake for BLAKE2b;
 - 1.29 cycles per byte on Skylake for BLAKE2bp;
 - 1.30 cycles per byte on Skylake for BLAKE2sp.
