# Description 

Initial SONIC proof system integration using the code from the [original implementation](https://github.com/zknuckles/sonic.git). It's here for experimental reasons and evaluation of the following properties:

- How applicable is "helped" procedure for a case of Ethereum
- What is a final verification cost for "helped" and "unhelped" procedures
- Prover efficiency in both cases
- Implementation of a memory constrained prover and helper
- Smart-contract implementation of verifiers
- Code cleanup
- Migration for smart-contract compatible transcripts

## TODO Plan

- [x] Test with public inputs
- [x] Test on BN256 
- [x] Parallelize using existing primitives
- [ ] Implement polynomial parallelized evaluation
- [ ] Make custom transcriptor that is easy to transform into the smart-contract
- [ ] Basic Ethereum smart-contract
- [ ] Add blinding factors
- [ ] Implement unhelped version