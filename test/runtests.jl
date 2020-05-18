using Jute
using LogProof
using Random
using DarkIntegers
using DarkCurves
using Curve25519

include("protocol.test.jl")
include("encryption.test.jl")

exit(runtests())
