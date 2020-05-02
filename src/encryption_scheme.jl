#=
An example encryption scheme (Section 1.5)
=#

function rand_polynomial(
        rng::AbstractRNG, ::Type{Z}, d::Int, B::Int=0) where Z
    Polynomial([rand_around_zero(rng, Z, B) for i in 1:d], negacyclic_modulus)
end


function noise_polynomial(
        rng::AbstractRNG, ::Type{Z}, d::Int, B::Int=0) where Z
    broadcast_into_polynomial(-, rand_polynomial(rng, Z, d, 2 * B), unsigned(B))
end


function scalar_polynomial(::Type{R}, val) where R <: Polynomial{Z, N} where {Z, N}
    coeffs = zeros(Z, N)
    coeffs[1] = convert(Z, val)
    Polynomial(coeffs, negacyclic_modulus)
end


get_types(params::ProofParams{Zq, Zp, G}) where {Zq, Zp, G} = Zq, Zp, G


struct EncryptionParams{Zq}
    proof_params :: ProofParams{Zq}
    noise_bound :: Int
    message_bound :: Int
    polynomial_order :: Int

    function EncryptionParams(q::Int, noise_bound::Int, message_bound::Int, polynomial_order::Int)
        proof_params = ProofParams(q)
        Zq, Zp, G = get_types(proof_params)
        new{Zq}(proof_params, noise_bound, message_bound, polynomial_order)
    end
end


function rand_message(rng, params::EncryptionParams{Z}) where Z
    rand_polynomial(rng, Z, params.polynomial_order, params.message_bound)
end


struct SecretKey{R <: Polynomial}
    params :: EncryptionParams
    s :: R
    e :: R

    function SecretKey(rng, params::EncryptionParams{Z}) where Z
        s = noise_polynomial(rng, Z, params.polynomial_order, params.noise_bound)
        e = noise_polynomial(rng, Z, params.polynomial_order, params.noise_bound)
        new{typeof(s)}(params, s, e)
    end
end


struct PublicKey{R <: Polynomial}
    params :: EncryptionParams
    a :: R
    t :: R

    function PublicKey(rng, sk::SecretKey{Polynomial{Z, N}}) where {Z, N}
        a = rand_polynomial(rng, Z, N)
        t = a * sk.s + sk.e
        new{Polynomial{Z, N}}(sk.params, a, t)
    end
end


struct Ciphertext{R <: Polynomial}
    u :: R
    v :: R
end


function encrypt(rng, pk::PublicKey{R}, m::R) where {R <: Polynomial{Z, N}} where {Z, N}
    @timeit timer "encryption" begin
        params = pk.params
        r = noise_polynomial(rng, Z, N, params.noise_bound)
        e1 = noise_polynomial(rng, Z, N, params.noise_bound)
        e2 = noise_polynomial(rng, Z, N, params.noise_bound)

        #@assert all(m.coeffs .< params.message_bound)

        p_big = convert(Z, params.message_bound)

        u = p_big * (pk.a * r + e1)
        v = p_big * (pk.t * r + e2) + m
    end

    @timeit timer "proof creation stage1" begin
        poly_zero = scalar_polynomial(R, 0)
        poly_one = scalar_polynomial(R, 1)
        poly_p = scalar_polynomial(R, p_big)
        A = [p_big*pk.a poly_p poly_zero poly_zero; p_big*pk.t poly_zero poly_p poly_one]
        S = collect(transpose([r e1 e2 m;]))
        T = collect(transpose([u v;]))
    end

    @timeit timer "proof creation stage2" begin
        vk = VerifierKnowledge(rng, params.proof_params, A, T, params.noise_bound)
    end

    # `A` can be transmitted just as `pk.a`, `pk.t` and `p`
    sz = size_estimate_without_A(vk) + size_estimate(pk.a) + size_estimate(pk.t) + size_estimate(Z)
    println("(verifier knowledge) prover -> verifier ", sz)

    pk = ProverKnowledge(vk, S)

    pk, Ciphertext{R}(u, v)
end


function central_mod(x::Z, p::T) where Z <: AbstractModUInt{T, M} where {T, M}
    x_val = value(x)
    half_mod = M >> 1

    is_negative = x_val > half_mod
    res = mod(is_negative ? M - x_val : x_val, p)

    res = if !is_negative || iszero(res)
        res
    else
        p - res
    end
    convert(Z, res)
end


function decrypt(
        sk::SecretKey{R}, ct::Ciphertext{R}
        ) where {R <: Polynomial{Z, N}} where {Z <: AbstractModUInt{T, M}, N} where {T, M}

    p = sk.params.message_bound
    res = ct.v - ct.u * sk.s
    broadcast_into_polynomial(central_mod, res, convert(T, p))
end
