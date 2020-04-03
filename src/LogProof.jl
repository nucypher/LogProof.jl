module LogProof

using Random
using Distributed
using SharedArrays
using DarkIntegers
using DarkCurves

include("actors.jl")
export run_pair

include("utils.jl")
export rand_around_zero

include("protocol_folding.jl")
include("protocol_inner_product.jl")

include("protocol_main.jl")
export prover_main_actor
export verifier_main_actor
export main_synchronous
export ProverKnowledge
export VerifierKnowledge
export ProofParams

include("encryption_scheme.jl")
export EncryptionParams
export SecretKey
export PublicKey
export encrypt
export decrypt
export rand_message

end
