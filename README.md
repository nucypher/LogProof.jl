# Log Proofs for RLWE ciphertexts

Master branch: [![CircleCI](https://circleci.com/gh/nucypher/LogProof.jl/tree/master.svg?style=svg)](https://circleci.com/gh/nucypher/LogProof.jl/tree/master) [![codecov](https://codecov.io/gh/nucypher/LogProof.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/nucypher/LogProof.jl)

This is a prototype implementation of the paper by R. Pino, V. Lyubashevsky, and G. Seiler, "Short Discrete Log Proofs for FHE and Ring-LWE Ciphertexts," [eprint 2019/057](https://eprint.iacr.org/2019/057).

The current implementation uses a pair of coroutines to simulate two parties without creating data structures to save intermediate state (see `src/actors.jl`).
A simple usage example can be found in `test/protocol.test.jl`:

```julia
# The size of the public matrix
n = 2
m = 3

# The second dimension of the secret matrix
k = 4

# The limit on the absolute value of any coefficient in the secret matrix
B = 10

rng = MersenneTwister(123)

A = make_A(rng, n, m) # create the public matrix of polynomials
S = make_S(rng, m, k, B) # create the secret matrix of polynomials

T = A * S # calculate their product

# This is what verifier knows
vk = VerifierKnowledge(rng, A, T, B)

# The prover knows whatever verifier knows and also the secret matrix `S`
pk = ProverKnowledge(vk, S)

# Run the protocol pair `prover()`/`verifier()`
run_pair(prover, verifier, (rng, pk), (rng, vk))
```
