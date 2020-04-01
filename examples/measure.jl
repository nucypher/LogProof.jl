using Profile
using LogProof
using Random
using DarkIntegers
using DarkCurves


function rand_Zq_polynomial(
        rng::AbstractRNG, params::Params{Zq, Zp, G}, d::Int, B::Int=0) where {Zq, Zp, G}
    Polynomial([rand_around_zero(rng, Zq, B) for i in 1:d], negacyclic_modulus)
end


function make_A(rng::AbstractRNG, params::Params, d::Int, rows::Int, cols::Int)
    [rand_Zq_polynomial(rng, params, d) for i in 1:rows, j in 1:cols]
end


function make_S(rng::AbstractRNG, params::Params, d::Int, rows::Int, cols::Int, B::Int)
    [
        broadcast_into_polynomial(-, rand_Zq_polynomial(rng, params, d, 2 * B), unsigned(B))
        for i in 1:rows, j in 1:cols]
end


get_test_types(params::Params{Zq, Zp, G}) where {Zq, Zp, G} = Zp, G


function main()

    params = Params(8191)
    Zp, G = get_test_types(params)

    n = 2
    m = 4
    k = 1
    B = 4

    rng = MersenneTwister(123)

    A = make_A(rng, params, 1024, n, m)
    S = make_S(rng, params, 1024, m, k, B)

    T = A * S

    vk = VerifierKnowledge(rng, params, A, T, B)
    pk = ProverKnowledge(vk, S)

    println("warm-up starting")
    @time main_synchronous(rng, pk, vk)
    println("warm-up done")

    LogProof.reset_stage_timer!()
    main_synchronous(rng, pk, vk)
    LogProof.display_stage_timer()
end


main()
