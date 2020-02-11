function next_power_of_2(x)
    2^ceil(Int, log2(x))
end


struct VerifierKnowledgeFolding
    g_vec :: Array{G, 1}
    h_vec :: Array{G, 1}
    a :: G
    u :: G
    t :: G

    function VerifierKnowledgeFolding(g_vec, h_vec, a, u, t)
        l = length(g_vec)
        np2 = next_power_of_2(l)
        if np2 != l
            g_vec = [g_vec; [one(G) for i in 1:(np2-l)]]
            h_vec = [h_vec; [one(G) for i in 1:(np2-l)]]
        end

        new(g_vec, h_vec, a, u, t)
    end
end


struct ProverKnowledgeFolding
    verifier_knowledge :: VerifierKnowledgeFolding
    v1_vec :: Array{Zp, 1}
    v2_vec :: Array{Zp, 1}
    rho :: Zp

    function ProverKnowledgeFolding(vk, v1_vec, v2_vec, rho)
        l = length(v1_vec)
        np2 = next_power_of_2(l)
        if np2 != l
            v1_vec = [v1_vec; [zero(Zp) for i in 1:(np2-l)]]
            v2_vec = [v2_vec; [zero(Zp) for i in 1:(np2-l)]]
        end

        new(vk, v1_vec, v2_vec, rho)
    end
end


struct FoldedVerifierKnowledge
    g :: G
    h :: G
    a :: G
    u :: G
    t_prime :: G
end


struct FoldedProverKnowledge
    verifier_knowledge :: FoldedVerifierKnowledge
    v1 :: Zp
    v2 :: Zp
    rho_prime :: Zp
end


function halves(v::Array{T, 1}) where T
    l = length(v) ÷ 2
    v[1:l], v[l+1:end]
end


function fold_commitment(vk::VerifierKnowledgeFolding, t_minus1::G, t_1::G, c::Zp)
    g_t_vec, g_b_vec = halves(vk.g_vec)
    h_t_vec, h_b_vec = halves(vk.h_vec)

    g_prime_vec = g_t_vec .* g_b_vec.^c
    h_prime_vec = h_t_vec .* h_b_vec.^inv(c)
    t_pprime = t_minus1^inv(c) * vk.t * t_1^c

    VerifierKnowledgeFolding(g_prime_vec, h_prime_vec, vk.a, vk.u, t_pprime)
end


struct FoldingPayloadStage1
    t_1 :: G
    t_minus1 :: G
end


struct FoldingPayloadStage2
    c :: Zp
end


function is_folded(pk::ProverKnowledgeFolding)
    is_folded(pk.verifier_knowledge)
end


function is_folded(vk::VerifierKnowledgeFolding)
    length(vk.g_vec) == 1
end


function finalize_folding(vk::VerifierKnowledgeFolding)
    FoldedVerifierKnowledge(vk.g_vec[1], vk.h_vec[1], vk.a, vk.u, vk.t)
end


function finalize_folding(pk::ProverKnowledgeFolding)
    fvk = finalize_folding(pk.verifier_knowledge)
    FoldedProverKnowledge(fvk, pk.v1_vec[1], pk.v2_vec[1], pk.rho)
end


struct ProverFoldingIntermediateState
    v1_t_vec :: Array{Zp, 1}
    v1_b_vec :: Array{Zp, 1}
    v2_t_vec :: Array{Zp, 1}
    v2_b_vec :: Array{Zp, 1}
    sigma_1 :: Zp
    sigma_minus1 :: Zp
end


function prover_folding_stage1(rng, pk::ProverKnowledgeFolding)
    vk = pk.verifier_knowledge

    g_t_vec, g_b_vec = halves(vk.g_vec)
    h_t_vec, h_b_vec = halves(vk.h_vec)
    v1_t_vec, v1_b_vec = halves(pk.v1_vec)
    v2_t_vec, v2_b_vec = halves(pk.v2_vec)

    sigma_minus1 = rand_Zp(rng)
    sigma_1 = rand_Zp(rng)

    t_minus1 = (
        prod(g_t_vec .^ v1_b_vec)
        * prod(h_b_vec .^ v2_t_vec)
        * vk.a^(v1_b_vec' * v2_t_vec)
        * vk.u^sigma_minus1)

    t_1 = (
        prod(g_b_vec .^ v1_t_vec)
        * prod(h_t_vec .^ v2_b_vec)
        * vk.a^(v1_t_vec' * v2_b_vec)
        * vk.u^sigma_1)

    state = ProverFoldingIntermediateState(v1_t_vec, v1_b_vec, v2_t_vec, v2_b_vec, sigma_1, sigma_minus1)
    payload = FoldingPayloadStage1(t_1, t_minus1)

    payload, state
end


function prover_folding_stage2(
        pk::ProverKnowledgeFolding,
        state::ProverFoldingIntermediateState,
        payload1::FoldingPayloadStage1, payload2::FoldingPayloadStage2)

    c = payload2.c

    new_vk = fold_commitment(pk.verifier_knowledge, payload1.t_minus1, payload1.t_1, c)

    v1_prime_vec = state.v1_t_vec + inv(c) * state.v1_b_vec
    v2_prime_vec = state.v2_t_vec + c * state.v2_b_vec

    rho_pprime = inv(c) * state.sigma_minus1 + pk.rho + c * state.sigma_1

    new_pk = ProverKnowledgeFolding(new_vk, v1_prime_vec, v2_prime_vec, rho_pprime)
end


function verifier_folding_stage1(rng)
    c = rand_Zp_nonzero(rng)
    FoldingPayloadStage2(c)
end


function verifier_folding_stage2(
        vk::VerifierKnowledgeFolding,
        payload1::FoldingPayloadStage1, payload2::FoldingPayloadStage2)
    fold_commitment(vk, payload1.t_minus1, payload1.t_1, payload2.c)
end


function folding_synchronous(rng, pk::ProverKnowledgeFolding, vk::VerifierKnowledgeFolding)
    while !is_folded(vk)
        payload1, state = prover_folding_stage1(rng, pk)
        payload2 = verifier_folding_stage1(rng)

        pk = prover_folding_stage2(pk, state, payload1, payload2)
        vk = verifier_folding_stage2(vk, payload1, payload2)
    end

    finalize_folding(pk), finalize_folding(vk)
end


function prover_folding_actor(channel::IOChannel, rng, pk::ProverKnowledgeFolding)

    if is_folded(pk)
        return finalize_folding(pk)
    end

    payload1, state = prover_folding_stage1(rng, pk)

    put!(channel, payload1)
    payload2 = take!(channel)

    new_pk = prover_folding_stage2(pk, state, payload1, payload2)

    prover_folding_actor(channel, rng, new_pk)
end


function verifier_folding_actor(channel::IOChannel, rng, vk::VerifierKnowledgeFolding)

    if is_folded(vk)
        return finalize_folding(vk)
    end

    payload1 = take!(channel)
    payload2 = verifier_folding_stage1(rng)
    put!(channel, payload2)

    new_vk = verifier_folding_stage2(vk, payload1, payload2)

    verifier_folding_actor(channel, rng, new_vk)
end
