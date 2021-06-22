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
cargo run --release -- NUMBER_OF_ACCUMULATORS_TO_UPDATE COUNTERS_TO_UPDATE_PER_ACCUMULATOR
```
E.g., to test performance of updating 1000 users' accumulators, each of which requires 100 updates, run
```
cargo run --release -- 1000 100
```

You should see some output of the form

```
Parameter precomputation (one time cost) (2.431505878s)

User:      Create BBA init request (653.833961ms)
Authority: Verify and sign initial accumulator (11.485175ms)
User:      Create BBA update request [100 counters updated] (368.676303ms)
Authority: Update BBA (3.225820922s for 1000 users, 3.22582ms per user)
User:      Process update response (609.066µs)
User:      Open BBA (191.299822ms)
------------------------------
Init proof size:    2309 bytes
Update proof size:  2437 bytes
Opening proof size: 2181 bytes
```
