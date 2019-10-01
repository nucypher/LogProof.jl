module LogProof

using Random

using DarkIntegers


include("actors.jl")
export run_pair

include("curve.jl")

include("utils.jl")
export rand_Zq_polynomial
export rand_G
export rand_Zp

include("protocol_folding.jl")
include("protocol_inner_product.jl")

include("protocol_main.jl")
export prover
export verifier
export ProverKnowledge
export VerifierKnowledge

end
