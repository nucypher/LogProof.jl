# Returns the negacyclic modulus (x^N+1) as a polynomial of length 2N
# TODO: cannot get the modulus from the type system at the moment
function extended_poynomial_modulus(::Type{Polynomial{T, N}}) where {T, N}
    f_coeffs = [one(T), zeros(T, N-1)..., one(T), zeros(T, N-1)...]
    # The modulus here does not matter since it's the extended length and we won't get over it.
    # Therefore just using `negacyclic_modulus` instead of `polynomial_modulus`
    Polynomial(f_coeffs, negacyclic_modulus)
end


struct VerifierKnowledge{Zq, Zp, G}
    params :: Params{Zq, Zp, G}
    A :: Array{<:Polynomial{Zq}, 2}
    T :: Array{<:Polynomial{Zq}, 2}
    polynomial_degree :: Int
    b :: Int
    b1 :: Int
    b2 :: Int
    l :: Int
    g_vec :: Array{G, 1}
    h_vec :: Array{G, 1}
    u :: G

    function VerifierKnowledge(
            rng, params::Params{Zq, Zp, G}, A::Array{P, 2}, T::Array{P, 2}, B::Int
            ) where {Zq, Zp, G, P <: Polynomial{Zq, N}} where N

        # TODO: cannot enforce it with type system at the moment
        # Hardcoding for now
        @assert all(x.modulus == negacyclic_modulus for x in A)
        @assert all(x.modulus == negacyclic_modulus for x in T)

        # The infinity norm of the negacyclic modulus that we use is just 1.
        polynomial_modulus_norm = 1

        n, m = size(A)
        n, k = size(T)

        q = as_builtin(modulus(Zq))

        b = ceil(Int, log2(B)) + 1
        b1 = ceil(Int, log2(m * N * B + N * polynomial_modulus_norm))
        b2 = ceil(Int, log2(q))
        l = m * k * N * b + n * k * (2 * N - 1) * b1 + n * k * (N - 1) * b2

        g_vec = [rand_point(rng, G) for i in 1:l]
        h_vec = [rand_point(rng, G) for i in 1:l]
        u = rand_point(rng, G)

        new{Zq, Zp, G}(params, A, T, N, b, b1, b2, l, g_vec, h_vec, u)
    end
end


struct ProverKnowledge{Zq, Zp, G}
    verifier_knowledge :: VerifierKnowledge{Zq, Zp, G}
    S :: Array{<:Polynomial{Zq}, 2}

    function ProverKnowledge(
            verifier_knowledge::VerifierKnowledge{Zq, Zp, G}, S::Array{<:Polynomial{Zq}, 2}
            ) where {Zq, Zp, G}

        # TODO: cannot enforce it with type system at the moment
        @assert all(x.modulus == negacyclic_modulus for x in S)

        new{Zq, Zp, G}(verifier_knowledge, S)
    end
end


# Converts a number modulo q in range (-q/2, q/2+1), stored as a positive integer in [0, q),
# to the same signed integer, but modulo p. That is, maps [0, q/2+1) to [0, q/2+1)
# and (-q/2 mod q, 0) to (-q/2 mod p, 0) (again, stored as a positive integer).
function expand(::Type{Zp}, x::Zq) where {Zp <: AbstractModUInt, Zq <: AbstractModUInt}
    x_val = value(x)
    res = convert(Zp, x_val)
    if x_val > (modulus(Zq) >> 1)
        res -= convert(Zp, modulus(Zq))
    end
    res
end
expand(::Type{Zp}, x::Polynomial{Zq}) where {Zp <: AbstractModUInt, Zq <: AbstractModUInt} =
    broadcast_into_polynomial(elem -> expand(Zp, elem), x)


# TODO: serves only debugging purpose, move to tests
function central(x::AbstractModUInt{T, M}) where {T, M}
    x_bi = convert(BigInt, value(x))
    p_bi = convert(BigInt, M)
    x_bi > p_bi ÷ 2 ? (x_bi - p_bi) : x_bi
end


# Find R1 and R2 such that A * S + q * R1 + f * R2 = T without taking any modulus
# (A, S, T with polynomials modulo f, and coefficients modulo q)
function find_residuals(
        ::Type{Zp}, A::Array{P, 2}, S::Array{P, 2}, T::Array{P, 2}
        ) where {Zp <: AbstractModUInt, P <: Polynomial{Zq, N}} where {N, Zq <: AbstractModUInt}

    A_exp = resize.(A, 2N)
    S_exp = resize.(S, 2N)
    T_exp = resize.(T, 2N)

    X1 = T_exp - A_exp * S_exp

    f_q = extended_poynomial_modulus(Polynomial{Zq, N})
    f_p = extended_poynomial_modulus(Polynomial{Zp, N})

    R2 = Array{Polynomial{Zq, 2N}}(undef, size(X1)...)
    Q = Array{Polynomial{Zq, 2N}}(undef, size(X1)...)
    for i in 1:size(X1, 1), j in 1:size(X1, 2)
        R2[i, j], Q[i, j] = divrem(X1[i, j], f_q)

        # TODO: move to tests
        @assert all(Q[i, j].coeffs .== 0)
        @assert all(R2[i, j].coeffs[N:end] .== 0)
    end

    n, m = size(A)
    B = 10
    bound = (m * N * B + N) ÷ 2

    expand_to_Zp = x -> expand(Zp, x)

    A_Zp = expand_to_Zp.(A_exp)
    S_Zp = expand_to_Zp.(S_exp)
    T_Zp = expand_to_Zp.(T_exp)
    R2_Zp = expand_to_Zp.(R2)

    X2 = T_Zp .- A_Zp * S_Zp .- f_p * R2_Zp

    q_p = convert(Zp, modulus(Zq))
    R1 = X2 .* inv(q_p)

    for i in 1:size(R1, 1), j in 1:size(R1, 2)
        # TODO: move to tests
        @assert all(central.(R1[i,j].coeffs) .<= bound)
    end

    @assert all(T_Zp .== A_Zp * S_Zp .+ f_p .* R2_Zp .+ q_p * R1)

    resize.(R1, 2*N-1), resize.(R2, N-1)
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


function commit(
        vk::VerifierKnowledge{Zq, Zp, G}, alpha::Zp, beta_vec::Array{Zp, 1},
        gamma_vec::Array{Zp, 1}, phi_vec::Array{Zp, 1}, psi::Zp, w::G) where {Zq, Zp, G}
    inverses = inv.(phi_vec)
    g_vec_prime = vk.g_vec .* inverses

    expand_to_Zp = x -> expand(Zp, x)

    d = vk.polynomial_degree
    q = convert(Zp, modulus(Zq))
    f = extended_poynomial_modulus(Polynomial{Zp, d})

    v_vec = vcat(
        outer(
            transpose(apply.(expand_to_Zp.(vk.A), alpha)) * gamma_vec,
            beta_vec,
            powers(alpha, d),
            powers_of_2(Zp, vk.b)),
        outer(
            q * gamma_vec,
            beta_vec,
            powers(alpha, 2 * d - 1),
            powers_of_2(Zp, vk.b1)),
        outer(
            apply.(f, alpha) .* gamma_vec,
            beta_vec,
            powers(alpha, d - 1),
            powers_of_2(Zp, vk.b2)))

    t = w + curve_lin_comb(g_vec_prime, v_vec .+ psi * phi_vec) + sum(vk.h_vec) * psi

    v_vec, t, g_vec_prime
end


struct MainPayload1{G}
    w :: G
end


struct MainPayload2{Zp}
    alpha :: Zp
    beta_vec :: Array{Zp, 1}
    gamma_vec :: Array{Zp, 1}
    phi_vec :: Array{Zp, 1}
    psi :: Zp
end


struct ProverMainIntermediateState{Zp}
    s1_vec :: BitArray
    s2_vec :: BitArray
    rho :: Zp
end


function prover_main_stage1(rng::AbstractRNG, pk::ProverKnowledge{Zq, Zp, G}) where {Zq, Zp, G}
    vk = pk.verifier_knowledge

    R1, R2 = find_residuals(Zp, vk.A, pk.S, vk.T)

    s_vec = serialize(pk.S)
    r1_vec = serialize(R1)
    r2_vec = serialize(R2)

    s1_vec = vcat(binary(s_vec, vk.b), binary(r1_vec, vk.b1), binary(r2_vec, vk.b2))
    s2_vec = xor.(s1_vec, ones(eltype(s1_vec), length(s1_vec)))

    rho = rand(rng, Zp)

    w = sum(mul_by_bool_vec(vk.g_vec, s2_vec)) + sum(mul_by_bool_vec(vk.h_vec, s1_vec)) + vk.u * rho

    payload = MainPayload1(w)
    state = ProverMainIntermediateState(s1_vec, s2_vec, rho)

    payload, state
end


function prover_main_stage2(
        pk::ProverKnowledge{Zq, Zp, G}, state::ProverMainIntermediateState{Zp},
        payload1::MainPayload1, payload2::MainPayload2) where {Zq, Zp, G}

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


function verifier_main_stage1(rng::AbstractRNG, vk::VerifierKnowledge{Zq, Zp, G}) where {Zq, Zp, G}
    n, m = size(vk.A)
    n, k = size(vk.T)

    alpha = rand_nonzero(rng, Zp)
    beta_vec = [rand_nonzero(rng, Zp) for i in 1:k]
    gamma_vec = [rand_nonzero(rng, Zp) for i in 1:n]
    phi_vec = [rand_nonzero(rng, Zp) for i in 1:vk.l]
    psi = rand_nonzero(rng, Zp)

    MainPayload2(alpha, beta_vec, gamma_vec, phi_vec, psi)
end


function verifier_main_stage2(
        vk::VerifierKnowledge{Zq, Zp, G}, payload1::MainPayload1{G}, payload2::MainPayload2{Zp}) where {Zq, Zp, G}

    v_vec, t, g_vec_prime = commit(
        vk, payload2.alpha, payload2.beta_vec, payload2.gamma_vec, payload2.phi_vec,
        payload2.psi, payload1.w)

    expand_to_Zp = x -> expand(Zp, x)

    x = (
        payload2.gamma_vec' * apply.(expand_to_Zp.(vk.T), payload2.alpha) * payload2.beta_vec +
        payload2.psi * sum(v_vec) +
        (payload2.psi + payload2.psi^2) * sum(payload2.phi_vec))

    VerifierKnowledgeInnerProduct(g_vec_prime, vk.h_vec, vk.u, t, x)
end


function main_synchronous(
        rng::AbstractRNG, pk::ProverKnowledge{Zq, Zp, G}, vk::VerifierKnowledge{Zq, Zp, G}) where {Zq, Zp, G}
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
