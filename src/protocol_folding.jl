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


function prover_folding(channel::IOChannel, rng, pk::ProverKnowledgeFolding)

    println("Prover - folding (length $(length(pk.verifier_knowledge.g_vec)))")

    vk = pk.verifier_knowledge
    l = length(vk.g_vec)

    if l == 1
        fvk = FoldedVerifierKnowledge(vk.g_vec[1], vk.h_vec[1], vk.a, vk.u, vk.t)
        fpk = FoldedProverKnowledge(fvk, pk.v1_vec[1], pk.v2_vec[1], pk.rho)
        return fpk
    end

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

    put!(channel, (t_minus1, t_1))
    c = take!(channel)

    new_vk = fold_commitment(vk, t_minus1, t_1, c)

    v1_prime_vec = v1_t_vec + inv(c) * v1_b_vec
    v2_prime_vec = v2_t_vec + c * v2_b_vec

    rho_pprime = inv(c) * sigma_minus1 + pk.rho + c * sigma_1

    new_pk = ProverKnowledgeFolding(new_vk, v1_prime_vec, v2_prime_vec, rho_pprime)

    prover_folding(channel, rng, new_pk)
end


function verifier_folding(channel::IOChannel, rng, vk::VerifierKnowledgeFolding)

    println("Verifier - folding (length $(length(vk.g_vec)))")

    l = length(vk.g_vec)

    if l == 1
        fvk = FoldedVerifierKnowledge(vk.g_vec[1], vk.h_vec[1], vk.a, vk.u, vk.t)
        return fvk
    end

    t_minus1, t_1 = take!(channel)
    c = rand_Zp_nonzero(rng)
    put!(channel, c)

    new_vk = fold_commitment(vk, t_minus1, t_1, c)

    verifier_folding(channel, rng, new_vk)
end
