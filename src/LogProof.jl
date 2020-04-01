module LogProof

using TimerOutputs
using Random

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
export Params
export rand_around_zero

include("protocol_folding.jl")
include("protocol_inner_product.jl")

include("protocol_main.jl")
export prover_main_actor
export verifier_main_actor
export main_synchronous
export ProverKnowledge
export VerifierKnowledge

end
