# BBA scheme

This PR implements a BBA scheme based on the scheme [described here](https://hackmd.io/@izzy/rJApOn5zu).

The major differences between that description and this implementation are

- Opening proofs do not perform the range checks on the counter values
- Opening proofs do not have a payout public-key as a public input
- Initialization uses a general-purpose zero-knowledge proof rather than a specialized Schnorr proof, which would be more efficient.
- The update proofs could probably be made 2x more efficient with a bit of optimization work.

## Building and running

1. Initialize submodules and install rust 1.45.2

```
git submodule update --init --recursive
rustup default 1.45.2
```

2. Run

```
cargo run --release
```

You should see some output of the form

```
Parameter precomputation (one time cost) (2.432729801s)

User:      Create BBA init request (653.064071ms)
Authority: Verify and sign initial accumulator (11.527393ms)
User:      Create BBA update request (362.221627ms)
Authority: Update BBA (7.979831ms)
User:      Process update response (1.005992ms)
User:      Open BBA (157.451082ms)
------------------------------
Init proof size:    2309 bytes
Update proof size:  2437 bytes
Opening proof size: 2181 bytes
```
