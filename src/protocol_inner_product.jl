struct VerifierKnowledgeInnerProduct
    g_vec :: Array{G, 1}
    h_vec :: Array{G, 1}
    u :: G
    t :: G
    x :: Zp
end


struct ProverKnowledgeInnerProduct
    verifier_knowledge :: VerifierKnowledgeInnerProduct
    v1_vec :: Array{Zp, 1}
    v2_vec :: Array{Zp, 1}
    rho :: Zp
end


function prover_inner_product(channel::IOChannel, rng, pk::ProverKnowledgeInnerProduct)

    a = take!(channel)

    vk = pk.verifier_knowledge

    t_prime = vk.t * a^vk.x

    vk = pk.verifier_knowledge

    vk_folding = VerifierKnowledgeFolding(vk.g_vec, vk.h_vec, a, vk.u, t_prime)
    pk_folding = ProverKnowledgeFolding(vk_folding, pk.v1_vec, pk.v2_vec, pk.rho)
    pk_folded = prover_folding(channel, rng, pk_folding)
    vk_folded = pk_folded.verifier_knowledge

    y1 = rand_Zp(rng)
    y2 = rand_Zp(rng)
    sigma = rand_Zp(rng)
    sigma_prime = rand_Zp(rng)

    v1 = pk_folded.v1
    v2 = pk_folded.v2
    rho_prime = pk_folded.rho_prime

    w = (
        vk_folded.g^y1 *
        vk_folded.h^y2 *
        vk_folded.a^(y1 * pk_folded.v2 + y2 * pk_folded.v1) *
        vk_folded.u^sigma)
    w_prime = vk_folded.a^(y1 * y2) * vk_folded.u^sigma_prime

    put!(channel, (w, w_prime))

    c = take!(channel)

    z1 = y1 + c * v1
    z2 = y2 + c * v2

    tau = c * rho_prime + sigma + inv(c) * sigma_prime

    put!(channel, (z1, z2, tau))
end


function verifier_inner_product(channel::IOChannel, rng, vk::VerifierKnowledgeInnerProduct)

    a = rand_G(rng)
    put!(channel, a)

    t_prime = vk.t * a^vk.x

    vk_folding = VerifierKnowledgeFolding(vk.g_vec, vk.h_vec, a, vk.u, t_prime)
    vk_folded = verifier_folding(channel, rng, vk_folding)

    w, w_prime = take!(channel)

    c = rand_Zp_nonzero(rng)

    put!(channel, c)

    z1, z2, tau = take!(channel)

    t_pprime = vk_folded.t_prime
    g = vk_folded.g
    h = vk_folded.h
    u = vk_folded.u
    a = vk_folded.a

    @assert t_pprime^c * w * w_prime^inv(c) == g^z1 * h^z2 * a^(inv(c) * z1 * z2) * u^tau
end
