using Jute
using LogProof
using Random
using DarkIntegers

include("curve.test.jl")
include("protocol.test.jl")

exit(runtests())
