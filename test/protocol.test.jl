using LogProof: rand_point


function rand_Zq_polynomial(
        rng::AbstractRNG, params::ProofParams{Zq, Zp, G}, d::Int, B::Int=0) where {Zq, Zp, G}
    Polynomial(rand_around_zero(rng, Zq, B, d), negacyclic_modulus)
end


function make_A(rng::AbstractRNG, params::ProofParams, d::Int, rows::Int, cols::Int)
    [rand_Zq_polynomial(rng, params, d) for i in 1:rows, j in 1:cols]
end


function make_S(rng::AbstractRNG, params::ProofParams, d::Int, rows::Int, cols::Int, B::Int)
    [
        broadcast_into_polynomial(-, rand_Zq_polynomial(rng, params, d, 2 * B), unsigned(B))
        for i in 1:rows, j in 1:cols]
end


get_test_types(params::ProofParams{Zq, Zp, G}) where {Zq, Zp, G} = Zp, G


curves = [Curve_secp256k1, RistrettoCurveVT] => ["SECP256k1", "Ristretto (var. time)"]


@testgroup "Protocol" begin


(@testcase "Inner product" for
        rng in fixed_rng(123),
        curve in curves,
        synchronous in ([false, true] => ["actors", "synchronous"])

    params = ProofParams(251, curve)
    Zp, G = get_test_types(params)

    l = 201
    g = rand_point(rng, G, l)
    h = rand_point(rng, G, l)
    u = rand_point(rng, G)
    v1 = rand(rng, Zp, l)
    v2 = rand(rng, Zp, l)
    rho = rand(rng, Zp)
    t = sum(g .* v1) + sum(h .* v2) + u * rho
    x = v1' * v2

    vk = LogProof.VerifierKnowledgeInnerProduct(g, h, u, t, x)
    pk = LogProof.ProverKnowledgeInnerProduct(vk, v1, v2, rho)

    if synchronous
        LogProof.inner_product_synchronous(rng, pk, vk)
    else
        run_pair(
            LogProof.prover_inner_product_actor, LogProof.verifier_inner_product_actor,
            (rng, pk), (rng, vk))
    end
end)


(@testcase "Folding" for
        rng in fixed_rng(123),
        curve in curves,
        synchronous in ([false, true] => ["actors", "synchronous"])

    params = ProofParams(251, curve)
    Zp, G = get_test_types(params)

    l = 8
    g = rand_point(rng, G, l)
    h = rand_point(rng, G, l)
    a = rand_point(rng, G)
    u = rand_point(rng, G)
    v1 = rand(rng, Zp, l)
    v2 = rand(rng, Zp, l)
    rho = rand(rng, Zp)
    t = sum(g .* v1) + sum(h .* v2) + a * (v1' * v2) + u * rho

    vk = LogProof.VerifierKnowledgeFolding(Zp, g, h, a, u, t)
    pk = LogProof.ProverKnowledgeFolding(vk, v1, v2, rho)

    if synchronous
        pkf, vkf = LogProof.folding_synchronous(rng, pk, vk)
    else
        pkf, vkf = run_pair(
            LogProof.prover_folding_actor, LogProof.verifier_folding_actor,
            (rng, pk), (rng, vk))
    end

    @assert vkf.t_prime == vkf.g * pkf.v1 + vkf.h * pkf.v2 + vkf.a * (pkf.v1 * pkf.v2) + vkf.u * (pkf.rho_prime)
end)


(@testcase "Main" for
        rng in fixed_rng(123),
        curve in curves,
        synchronous in ([false, true] => ["actors", "synchronous"])

    params = ProofParams(251)

    n = 2
    m = 3
    k = 4
    B = 7

    A = make_A(rng, params, 8, n, m)
    S = make_S(rng, params, 8, m, k, B)

    T = A * S

    vk = VerifierKnowledge(rng, params, A, T, B)
    pk = ProverKnowledge(vk, S)

    if synchronous
        run_pair(prover_main_actor, verifier_main_actor, (rng, pk), (rng, vk))
    else
        main_synchronous(rng, pk, vk)
    end
end)


end
