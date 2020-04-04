# Log Proofs for RLWE ciphertexts

Master branch: [![CircleCI](https://circleci.com/gh/nucypher/LogProof.jl/tree/master.svg?style=svg)](https://circleci.com/gh/nucypher/LogProof.jl/tree/master) [![codecov](https://codecov.io/gh/nucypher/LogProof.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/nucypher/LogProof.jl)

This is a prototype implementation of the paper by R. Pino, V. Lyubashevsky, and G. Seiler, "Short Discrete Log Proofs for FHE and Ring-LWE Ciphertexts," [eprint 2019/057](https://eprint.iacr.org/2019/057).

The current implementation uses a pair of coroutines to simulate two parties without creating data structures to save intermediate state (see `src/actors.jl`).
Alternatively, `_synchronous` functions can be used to run both prover and verifier in one thread (makes it easier to profile and debug).
A simple usage example can be found in `examples/example.jl`, demonstrating the usage of the proof itself and the example encryption scheme from Section 1.5 of the paper:

```julia
rng = MersenneTwister(123)

# 8191 - the example encryption scheme modulus
# 4 - bound on noises used for encryption
# 2 - bound on the message
# 1024 - polynomial degree
params = EncryptionParams(8191, 4, 2, 1024)

skey = SecretKey(rng, params)
pkey = PublicKey(rng, skey)

m = rand_message(rng, params)

# Encrypt the message
pk, ct = encrypt(rng, pkey, m)

# Run an encryption proof synchronously (prover and verifier are executed one at a time)
main_synchronous(rng, pk, pk.verifier_knowledge)

# decrypt the message
m_back = decrypt(skey, ct)

@assert m == m_back
```
