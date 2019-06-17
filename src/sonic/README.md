# Description 

Initial SONIC proof system integration using the code from the [original implementation](https://github.com/zknuckles/sonic.git). It's here for experimental reasons and evaluation of the following properties:

- How applicable is "helped" procedure for a case of Ethereum
- What is a final verification cost for "helped" and "unhelped" procedures
- Prover efficiency in both cases
- Implementation of a memory constrained prover and helper
- Smart-contract implementation of verifiers
- Code cleanup
- Migration for smart-contract compatible transcripts

## Current state

Beta - fast and valid, but breaking API changes are expected

## Completed

- Basic proof modes (helped/unhelped)
- Succinct `S` polynomial evaluation using permutation argument
- High-level API for non-succinct mode that can produce "large enough" SRS from a "global" SRS
- Proving/verifying keys that have additional information about the circuit such as number of gates, linear constraints and public inputs
- Implement non-assigning backends for faster estimation of circuit parameters in un-cached cases

## TODO Plan
- [ ] Make caching proving/verifying key for succinct mode
- [ ] Fix high-level API for both modes
- [ ] Re-structure the package itself