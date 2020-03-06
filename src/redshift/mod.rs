//abstraction of domains: interpolation, generators, interators e.t.c
pub mod domains;
//different rountnes to perform effective FFT
pub mod fft;
//different abstractions for an oracle, commitments, etc
pub mod IOP;
pub mod partial_reduction_field;
pub mod polynomials;
//main functions are here
pub mod redshift;
pub mod tester;