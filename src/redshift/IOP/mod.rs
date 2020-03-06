// channel is used to perform Fiat-Shamit heurestics: it consumes prover's commitments
// and responds with challenge
pub mod channel;
pub mod FRI;
// location for various types of hash function used inside channel (as an inner prng)
// and for constructoion of Merklee tree
pub mod hashes;
// it is an abstraction layer over concrete representation of oracle in IOP protocols
// for now there is only one effective construction - Merklee trees
// but who knows what will happen in the future, i.t. somebody will come uo with a new cool vector accumulator
pub mod oracle;