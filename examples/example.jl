using LogProof
using Random


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
