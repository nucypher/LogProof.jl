using Base.Iterators: product


struct VerifierKnowledge
    A :: Array{Rq, 2}
    T :: Array{Rq, 2}
    b :: Int
    b1 :: Int
    b2 :: Int
    l :: Int
    g_vec :: Array{G, 1}
    h_vec :: Array{G, 1}
    u :: G

    function VerifierKnowledge(rng, A::Array{<:Rq, 2}, T::Array{<:Rq, 2}, B::Int)

        n, m = size(A)
        n, k = size(T)

        b = ceil(Int, log2(B)) + 1
        b1 = ceil(Int, log2(m * d * B + d * f_norm))
        b2 = ceil(Int, log2(q))
        l = m * k * d * b + n * k * (2 * d - 1) * b1 + n * k * (d - 1) * b2

        g_vec = [rand_G(rng) for i in 1:l]
        h_vec = [rand_G(rng) for i in 1:l]
        u = rand_G(rng)

        new(A, T, b, b1, b2, l, g_vec, h_vec, u)
    end
end


struct ProverKnowledge
    verifier_knowledge :: VerifierKnowledge
    S :: Array{Rq, 2}
end


to_zp(x::Zq) = convert(Zp, value(x)) - (x > q ÷ 2 ? q : 0)
to_zp(x::Polynomial{Zq}) = Polynomial(to_zp.(x.coeffs), x.modulus)

central(x::Zq) = big(x) > big(q) ÷ 2 ? (big(x) - big(q)) : big(x)
function central(x::Zp)
    x_bi = convert(BigInt, value(x))
    p_bi = convert(BigInt, p)
    x_bi > p_bi ÷ 2 ? (x_bi - p_bi) : x_bi
end


# Find R1 and R2 such that A * S + q * R1 + f * R2 = T without taking any modulus
# (A, S, T with polynomials modulo f, and coefficients modulo q)
function find_residuals(A::Array{P, 2}, S::Array{P, 2}, T::Array{P, 2}) where P <: Rq

    A_exp = resize.(A, 2d)
    S_exp = resize.(S, 2d)
    T_exp = resize.(T, 2d)

    X1 = T_exp - A_exp * S_exp

    f_q = Polynomial(
        convert.(Zq, vcat([1], zeros(Int, d-1), [1], zeros(Int, d-1))), negacyclic_modulus)

    R2 = Array{eltype(A_exp)}(undef, size(X1)...)
    Q = Array{eltype(A_exp)}(undef, size(X1)...)
    for i in 1:size(X1, 1), j in 1:size(X1, 2)
        R2[i, j], Q[i, j] = divrem(X1[i, j], f_q)
        @assert all(Q[i, j].coeffs .== 0)
        @assert all(R2[i, j].coeffs[d:end] .== 0)
    end

    n, m = size(A)
    B = 10
    bound = (m * d * B + d) ÷ 2

    A_Zp = to_zp.(A_exp)
    S_Zp = to_zp.(S_exp)
    T_Zp = to_zp.(T_exp)
    R2_Zp = to_zp.(R2)

    X2 = T_Zp .- A_Zp * S_Zp .- f_exp * R2_Zp

    q_p = convert(Zp, q)
    R1 = X2 .* inv(q_p)

    for i in 1:size(R1, 1), j in 1:size(R1, 2)
        @assert all(central.(R1[i,j].coeffs) .<= bound)
    end

    @assert all(T_Zp .== A_Zp * S_Zp .+ f_exp .* R2_Zp .+ q_p * R1)

    resize.(R1, 2*d-1), resize.(R2, d-1)
end


function serialize(m::Array{T, 2}) where T
    # NOTE: matrices in Julia are stored in column-major order, and Serialize() in the paper
    # serializes in row-major order. But it doesn't matter as long as serialization
    # is performed in the same way in the prover and the verifier.
    vcat(serialize.(permutedims(m)[:])...)
end

serialize(p::Polynomial) = p.coeffs


function mul_by_bool_vec(a::Array{T, 1}, v::BitArray{1}) where T
    @assert length(a) == length(v)
    [v[i] ? a[i] : zero(T) for i in 1:length(a)]
end


function exp_to_bool_vec(a::Array{T, 1}, v::BitArray{1}) where T
    @assert length(a) == length(v)
    res = zero(T)
    for i in 1:length(a)
        if v[i]
            res += a[i]
        end
    end
    res
end


function powers(a, d)
    a .^ (0:d-1)
end


function outer(v1::Array{T, 1}, v2::Array{T, 1}, v3::Array{T, 1}, v4::Array{T, 1}) where T
    # If necessary can be implemented for an arbitrary number of vectors
    # using a generated functions, but that's too much complexity.
    res = (
        reshape(v4, length(v4), 1, 1, 1) .*
        reshape(v3, 1, length(v3), 1, 1) .*
        reshape(v2, 1, 1, length(v2), 1) .*
        reshape(v1, 1, 1, 1, length(v1)))
    res[:]
end


function commit(vk::VerifierKnowledge, alpha, beta_vec, gamma_vec, phi_vec, psi, w)
    inverses = inv.(phi_vec)
    g_vec_prime = vk.g_vec .* inverses

    v_vec = vcat(
        outer(
            transpose(apply.(to_zp.(vk.A), alpha)) * gamma_vec,
            beta_vec,
            powers(alpha, d),
            powers_of_2(Zp, vk.b)),
        outer(
            q * gamma_vec,
            beta_vec,
            powers(alpha, 2 * d - 1),
            powers_of_2(Zp, vk.b1)),
        outer(
            apply.(f_exp, alpha) .* gamma_vec,
            beta_vec,
            powers(alpha, d - 1),
            powers_of_2(Zp, vk.b2)))

    t = w + sum(g_vec_prime .* (v_vec .+ psi * phi_vec)) + sum(vk.h_vec .* psi)

    v_vec, t, g_vec_prime
end


struct MainPayload1
    w :: G
end


struct MainPayload2
    alpha :: Zp
    beta_vec :: Array{Zp, 1}
    gamma_vec :: Array{Zp, 1}
    phi_vec :: Array{Zp, 1}
    psi :: Zp
end


struct ProverMainIntermediateState
    s1_vec :: BitArray
    s2_vec :: BitArray
    rho :: Zp
end


function prover_main_stage1(rng::AbstractRNG, pk::ProverKnowledge)
    vk = pk.verifier_knowledge

    R1, R2 = find_residuals(vk.A, pk.S, vk.T)

    s_vec = serialize(pk.S)
    r1_vec = serialize(R1)
    r2_vec = serialize(R2)

    s1_vec = vcat(binary(s_vec, vk.b), binary(r1_vec, vk.b1), binary(r2_vec, vk.b2))
    s2_vec = xor.(s1_vec, ones(eltype(s1_vec), length(s1_vec)))

    rho = rand_Zp(rng)

    w = exp_to_bool_vec(vk.g_vec, s2_vec) + exp_to_bool_vec(vk.h_vec, s1_vec) + vk.u * rho

    payload = MainPayload1(w)
    state = ProverMainIntermediateState(s1_vec, s2_vec, rho)

    payload, state
end


function prover_main_stage2(
        pk::ProverKnowledge, state::ProverMainIntermediateState,
        payload1::MainPayload1, payload2::MainPayload2)

    vk = pk.verifier_knowledge

    v_vec, t, g_vec_prime = commit(
        vk, payload2.alpha, payload2.beta_vec, payload2.gamma_vec, payload2.phi_vec,
        payload2.psi, payload1.w)

    v1_vec = v_vec .+ mul_by_bool_vec(payload2.phi_vec, state.s2_vec) .+ payload2.phi_vec .* payload2.psi
    v2_vec = convert.(Zp, state.s1_vec) .+ payload2.psi
    x = v1_vec' * v2_vec

    vk = VerifierKnowledgeInnerProduct(g_vec_prime, vk.h_vec, vk.u, t, x)
    ProverKnowledgeInnerProduct(vk, v1_vec, v2_vec, state.rho)
end


function verifier_main_stage1(rng::AbstractRNG, vk::VerifierKnowledge)
    n, m = size(vk.A)
    n, k = size(vk.T)

    alpha = rand_Zp_nonzero(rng)
    beta_vec = [rand_Zp_nonzero(rng) for i in 1:k]
    gamma_vec = [rand_Zp_nonzero(rng) for i in 1:n]
    phi_vec = [rand_Zp_nonzero(rng) for i in 1:vk.l]
    psi = rand_Zp_nonzero(rng)

    MainPayload2(alpha, beta_vec, gamma_vec, phi_vec, psi)
end


function verifier_main_stage2(vk::VerifierKnowledge, payload1::MainPayload1, payload2::MainPayload2)
    v_vec, t, g_vec_prime = commit(
        vk, payload2.alpha, payload2.beta_vec, payload2.gamma_vec, payload2.phi_vec,
        payload2.psi, payload1.w)

    x = (
        payload2.gamma_vec' * apply.(to_zp.(vk.T), payload2.alpha) * payload2.beta_vec +
        payload2.psi * sum(v_vec) +
        (payload2.psi + payload2.psi^2) * sum(payload2.phi_vec))

    VerifierKnowledgeInnerProduct(g_vec_prime, vk.h_vec, vk.u, t, x)
end


function main_synchronous(rng::AbstractRNG, pk::ProverKnowledge, vk::VerifierKnowledge)
    payload1, state = prover_main_stage1(rng, pk)
    payload2 = verifier_main_stage1(rng, vk)
    pk_ip = prover_main_stage2(pk, state, payload1, payload2)
    vk_ip = verifier_main_stage2(vk, payload1, payload2)
    inner_product_synchronous(rng, pk_ip, vk_ip)
end


function prover_main_actor(channel::IOChannel, rng::AbstractRNG, pk::ProverKnowledge)
    payload1, state = prover_main_stage1(rng, pk)
    put!(channel, payload1)
    payload2 = take!(channel)
    pk_ip = prover_main_stage2(pk, state, payload1, payload2)
    prover_inner_product_actor(channel, rng, pk_ip)
end


function verifier_main_actor(channel::IOChannel, rng::AbstractRNG, vk::VerifierKnowledge)
    payload1 = take!(channel)
    payload2 = verifier_main_stage1(rng, vk)
    put!(channel, payload2)
    vk_ip = verifier_main_stage2(vk, payload1, payload2)
    verifier_inner_product_actor(channel, rng, vk_ip)
end
