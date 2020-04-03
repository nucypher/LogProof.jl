using Jute
using LogProof
using Random
using DarkIntegers

include("protocol.test.jl")
include("encryption.test.jl")

exit(runtests())
