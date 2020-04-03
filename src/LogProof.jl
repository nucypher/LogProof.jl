module LogProof

using TimerOutputs
using Random
using Distributed
using SharedArrays
using DarkIntegers
using DarkCurves

timer = TimerOutput()

reset_stage_timer!() = reset_timer!(timer)
function display_stage_timer()
    display(timer)
    println()
end


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
