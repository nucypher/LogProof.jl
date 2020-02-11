function make_A(rng::AbstractRNG, rows::Int, cols::Int)
    [rand_Zq_polynomial(rng) for i in 1:rows, j in 1:cols]
end


function make_S(rng::AbstractRNG, rows::Int, cols::Int, B::Int)
    [
        broadcast_into_polynomial(-, rand_Zq_polynomial(rng, 2 * B), unsigned(B))
        for i in 1:rows, j in 1:cols]
end


@testgroup "Protocol" begin


@testcase "Inner product" begin
    rng = MersenneTwister(123)

    l = 201
    g = [rand_G(rng) for i in 1:l]
    h = [rand_G(rng) for i in 1:l]
    u = rand_G(rng)
    v1 = [rand_Zp(rng) for i in 1:l]
    v2 = [rand_Zp(rng) for i in 1:l]
    rho = rand_Zp(rng)
    t = prod(g .^ v1) * prod(h .^ v2) * u^rho
    x = v1' * v2

    vk = LogProof.VerifierKnowledgeInnerProduct(g, h, u, t, x)
    pk = LogProof.ProverKnowledgeInnerProduct(vk, v1, v2, rho)
    run_pair(LogProof.prover_inner_product, LogProof.verifier_inner_product, (rng, pk), (rng, vk))
end


@testcase "Folding" for synchronous in ([false, true] => ["actors", "synchronous"])
    rng = MersenneTwister(123)

    l = 8
    g = [rand_G(rng) for i in 1:l]
    h = [rand_G(rng) for i in 1:l]
    a = rand_G(rng)
    u = rand_G(rng)
    v1 = [rand_Zp(rng) for i in 1:l]
    v2 = [rand_Zp(rng) for i in 1:l]
    rho = rand_Zp(rng)
    t = prod(g .^ v1) * prod(h .^ v2) * a^(v1' * v2) * u^rho

    vk = LogProof.VerifierKnowledgeFolding(g, h, a, u, t)
    pk = LogProof.ProverKnowledgeFolding(vk, v1, v2, rho)

    if synchronous
        pkf, vkf = LogProof.folding_synchronous(rng, pk, vk)
    else
        pkf, vkf = run_pair(
            LogProof.prover_folding_actor, LogProof.verifier_folding_actor,
            (rng, pk), (rng, vk))
    end

    @assert vkf.t_prime == vkf.g^pkf.v1 * vkf.h^pkf.v2 * vkf.a^(pkf.v1 * pkf.v2) * vkf.u^(pkf.rho_prime)
end


@testcase "Full" begin
    n = 2
    m = 3
    k = 4
    B = 7

    rng = MersenneTwister(123)

    A = make_A(rng, n, m)
    S = make_S(rng, m, k, B)

    T = A * S

    vk = VerifierKnowledge(rng, A, T, B)
    pk = ProverKnowledge(vk, S)

    run_pair(prover, verifier, (rng, pk), (rng, vk))
end


end
