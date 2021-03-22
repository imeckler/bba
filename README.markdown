# BBA scheme

This PR implements a BBA scheme based on the scheme [described here](https://hackmd.io/@izzy/rJApOn5zu).

The major differences between that description and this implementation are

- Opening proofs do not perform the range checks on the counter values
- Opening proofs do not have a payout public-key as a public input
- Initialization uses a general-purpose zero-knowledge proof rather than a specialized Schnorr proof, which would be more efficient.
- The update proofs could probably be made 2x more efficient with a bit of optimization work.
