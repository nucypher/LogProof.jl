# in the centered representation the range of Z* is [-half_mod, half_mod]
half_mod(::Type{T}) where T <: AbstractModUInt = convert(T, modulus(T) >> 1)


function rand_around_zero(
        rng::AbstractRNG, ::Type{Z}, B::Int=0, dims...
        ) where Z <: AbstractModUInt{T, M} where {T, M}
    if B == 0
        res = rand(rng, Z, dims...)
    else
        # TODO: or is it supposed to be the range (-B, B)?
        res = rand(rng, zero(Z):convert(Z, B-1), dims...)
    end
end


function rand_nonzero(rng::AbstractRNG, ::Type{Z}, dims...) where Z <: AbstractModUInt{T, M} where {T, M}
    rand(rng, one(Z):-one(Z), dims...)
end


function _rand_point(seed::UInt64, ::Type{G}, dim) where G
    rng = MersenneTwister(seed)
    rand(rng, G, dim)
end


rand_point(rng::AbstractRNG, ::Type{G}) where G = rand(rng, G)


function rand_point(rng::AbstractRNG, ::Type{G}, dim) where G <: EllipticCurvePoint
    nw = nworkers()
    if nw == 1 || nw > dim
        return rand(rng, G, dim)
    end

    dims = splay_len(dim, nw)

    # Technically not secure, but neither is MersenneTwister.
    # Makes the results reproducible.
    seeds = rand(rng, UInt64, nw)

    vcat(pmap(_rand_point, seeds, repeat([G], nw), dims)...)
end


# returns the degree of the polynomial
# (index of the maximum power of X with nonzero coefficient minus 1)
function polynomial_degree(p::Polynomial)
    res = findlast(x -> !iszero(x), p.coeffs)
    if !(res === nothing)
        res - 1
    else
        -1
    end
end


function Base.divrem(p::Polynomial{T}, f::Polynomial{T}) where T

    r = copy(p)
    r.coeffs .= zero(T)

    f_deg = polynomial_degree(f)

    while true
        p_deg = polynomial_degree(p)

        if f_deg > p_deg
            return r, p
        end

        # TODO (see issue #6 of DarkIntegers): assuming here that there is no remainder
        c = p.coeffs[p_deg + 1] ÷ f.coeffs[f_deg + 1]

        p -= mul_by_monomial(f, p_deg - f_deg) * c
        r.coeffs[p_deg - f_deg + 1] = c
    end
end


function apply(p::Polynomial{T}, alpha::T) where T
    sum(p.coeffs .* alpha .^ (0:length(p.coeffs)-1))
end


Base.copy(p::Polynomial) = Polynomial(copy(p.coeffs), p.modulus)


"""
Convert a number `z in [2^(b-1), 2^(b-1))` to its binary representation such that
`z = z_0 + z_1 * 2 + z_2 * 2^2 + ... + z_{b-2} * 2^(b-2) - z_{b-1} * 2^(b-1)`
"""
function binary(val::T, b::Int) where T <: AbstractModUInt
    # Note that we're getting numbers in Zq or Zp, (with possibly 2^b>q)
    # but the resulting contract must be valid in Zp
    # TODO: (issue #1) performance can be improved
    x = value(val)
    is_negative = x > value(half_mod(T))
    if is_negative
        val += 1 << (b-1) # adding an offset and treating it as a positive number
        x = value(val)
    end
    res = BitArray{1}(undef, b)
    for i in 1:(b-1)
        res[i] = isodd(x)
        x >>= 1
    end
    if !iszero(x)
        error("Value $val is greater than $b bits")
    end
    res[end] = is_negative # effectively subtracting the offset
    res
end

binary(val::AbstractArray, b::Int) = vcat([binary(x, b) for x in val]...)


# Returns what in the paper is denoted as
# `2_b = (1, 2, ... , 2^(b−2), −2^(b−1))'`
function powers_of_2(::Type{T}, d) where T
    res = convert(T, 2) .^ (0:d-1)
    res[end] = -res[end]
    res
end


function splay(arr::AbstractArray{T, 1}, nw) where T
    chunk_size, remainder = divrem(length(arr), nw)
    result = Array{Array{T, 1}}(undef, nw)
    for i in 1:nw
        start = (i - 1) * chunk_size + 1 + min(i - 1, remainder)
        stop = start + chunk_size - 1 + (i <= remainder ? 1 : 0)
        result[i] = arr[start:stop]
    end
    result
end


function splay_len(len::Int, nw)
    chunk_size, remainder = divrem(len, nw)
    [chunk_size + (i <= remainder ? 1 : 0) for i in 1:nw]
end


function lin_comb_mp(
        points::Array{P, 1}, coeffs::Array{T, 1}, w::Int=4) where {P <: EllipticCurvePoint, T <: Integer}
    nw = nworkers()
    if nw == 1 || nw > length(points)
        return lin_comb(points, coeffs, w)
    end
    point_chunks = splay(points, nw)
    coeff_chunks = splay(coeffs, nw)
    sum(pmap(lin_comb, point_chunks, coeff_chunks, repeat([w], nw)))
end


function batch_mul_mp(
        points::Array{P, 1}, coeff::T, w::Int=4,
        ) where {P <: EllipticCurvePoint, T <: Integer}
    nw = nworkers()
    if nw == 1 || nw > length(points)
        return batch_mul(points, coeff, w)
    end
    point_chunks = splay(points, nw)
    vcat(pmap(batch_mul, point_chunks, repeat([coeff], nw), repeat([w], nw))...)
end


function mul_by_inv_mp(g_vec::Array{G, 1}, phi_vec::Array{Zp, 1}) where {Zp, G}
    if nworkers() == 1
        return g_vec .* inv.(phi_vec)
    end

    g_vec_prime = SharedArray{G}(length(g_vec))
    @sync @distributed for i in 1:length(g_vec)
        g_vec_prime[i] = g_vec[i] * inv(phi_vec[i])
    end
    sdata(g_vec_prime)
end
