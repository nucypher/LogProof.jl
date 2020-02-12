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


struct InnerProductPayload1
    a :: G
end


struct InnerProductPayload2
    w :: G
    w_prime :: G
end


struct InnerProductPayload3
    c :: Zp
end


struct InnerProductPayload4
    z1 :: Zp
    z2 :: Zp
    tau :: Zp
end


struct ProverInnerProductIntermediateState
    y1 :: Zp
    y2 :: Zp
    sigma :: Zp
    sigma_prime :: Zp
end


function prover_inner_product_stage1(
        pk::ProverKnowledgeInnerProduct, payload1::InnerProductPayload1)

    a = payload1.a

    vk = pk.verifier_knowledge

    t_prime = vk.t * a^vk.x

    vk_folding = VerifierKnowledgeFolding(vk.g_vec, vk.h_vec, a, vk.u, t_prime)
    ProverKnowledgeFolding(vk_folding, pk.v1_vec, pk.v2_vec, pk.rho)
end


function prover_inner_product_stage2(rng, pk_folded::FoldedProverKnowledge)

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

    payload = InnerProductPayload2(w, w_prime)
    state = ProverInnerProductIntermediateState(y1, y2, sigma, sigma_prime)

    payload, state
end


function prover_inner_product_stage3(
        state::ProverInnerProductIntermediateState,
        pk_folded::FoldedProverKnowledge, payload3::InnerProductPayload3)

    c = payload3.c

    v1 = pk_folded.v1
    v2 = pk_folded.v2
    rho_prime = pk_folded.rho_prime

    z1 = state.y1 + c * v1
    z2 = state.y2 + c * v2

    tau = c * rho_prime + state.sigma + inv(c) * state.sigma_prime

    InnerProductPayload4(z1, z2, tau)
end


function verifier_inner_product_stage1(rng)
    InnerProductPayload1(rand_G(rng))
end


function verifier_inner_product_stage2(
        vk::VerifierKnowledgeInnerProduct, payload1::InnerProductPayload1)

    a = payload1.a

    t_prime = vk.t * a^vk.x

    VerifierKnowledgeFolding(vk.g_vec, vk.h_vec, a, vk.u, t_prime)
end


function verifier_inner_product_stage3(rng)
    c = rand_Zp_nonzero(rng)
    InnerProductPayload3(c)
end


function verifier_inner_product_stage4(
        vk_folded::FoldedVerifierKnowledge,
        payload2::InnerProductPayload2, payload3::InnerProductPayload3, payload4::InnerProductPayload4)

    t_pprime = vk_folded.t_prime
    g = vk_folded.g
    h = vk_folded.h
    u = vk_folded.u
    a = vk_folded.a

    w = payload2.w
    w_prime = payload2.w_prime

    c = payload3.c

    z1 = payload4.z1
    z2 = payload4.z2
    tau = payload4.tau

    @assert t_pprime^c * w * w_prime^inv(c) == g^z1 * h^z2 * a^(inv(c) * z1 * z2) * u^tau
end


function inner_product_synchronous(
        rng, pk::ProverKnowledgeInnerProduct, vk::VerifierKnowledgeInnerProduct)
    payload1 = verifier_inner_product_stage1(rng)
    pk_folding = prover_inner_product_stage1(pk, payload1)
    vk_folding = verifier_inner_product_stage2(vk, payload1)

    pkf, vkf = folding_synchronous(rng, pk_folding, vk_folding)

    payload2, state = prover_inner_product_stage2(rng, pkf)
    payload3 = verifier_inner_product_stage3(rng)

    payload4 = prover_inner_product_stage3(state, pkf, payload3)
    verifier_inner_product_stage4(vkf, payload2, payload3, payload4)
end


function prover_inner_product_actor(channel::IOChannel, rng, pk::ProverKnowledgeInnerProduct)
    payload1 = take!(channel)
    pk_folding = prover_inner_product_stage1(pk, payload1)
    pkf = prover_folding_actor(channel, rng, pk_folding)
    payload2, state = prover_inner_product_stage2(rng, pkf)
    put!(channel, payload2)
    payload3 = take!(channel)
    payload4 = prover_inner_product_stage3(state, pkf, payload3)
    put!(channel, payload4)
end


function verifier_inner_product_actor(channel::IOChannel, rng, vk::VerifierKnowledgeInnerProduct)
    payload1 = verifier_inner_product_stage1(rng)
    put!(channel, payload1)
    vk_folding = verifier_inner_product_stage2(vk, payload1)
    vkf = verifier_folding_actor(channel, rng, vk_folding)
    payload2 = take!(channel)
    payload3 = verifier_inner_product_stage3(rng)
    put!(channel, payload3)
    payload4 = take!(channel)
    verifier_inner_product_stage4(vkf, payload2, payload3, payload4)
end
