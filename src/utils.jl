struct Params{Zq <: AbstractModUInt, Zp <: AbstractModUInt, G}

    function Params(q::Int, point_coords::Type=JacobianPoint)
        q_tp = UInt64
        Zq = ModUInt{q_tp, convert(q_tp, q)}

        curve = Curve_secp256k1

        p_tp = MLUInt{4, UInt64}
        p = convert(p_tp, curve_order(curve))
        Zp = ModUInt{p_tp, convert(p_tp, p)}

        # p is prime, so NTT multiplication will be used automatically,
        # and finding a generator for a 256-bit prime takes a long time.
        # Use Karatsuba for simplicity.
        @eval DarkIntegers.known_polynomial_mul_function(
            ::Type{$Zp}, ::Val{N}, ::DarkIntegers.NegacyclicModulus) where N = DarkIntegers.karatsuba_mul

        curve_tp = curve_scalar_type(curve, MgModUInt, p_tp)
        G = point_coords{curve, curve_tp}

        f_norm = 1 # we're using negacyclic polynomials, so it is the norm of `x^N + 1`

        new{Zq, Zp, G}()
    end
end


# in the centered representation the range of Z* is [-half_mod, half_mod]
half_mod(::Type{T}) where T <: AbstractModUInt = convert(T, modulus(T) >> 1)


function rand_around_zero(rng::AbstractRNG, ::Type{Z}, B::Int=0) where Z <: AbstractModUInt{T, M} where {T, M}
    if B == 0
        res = rand(rng, zero(T):(M - one(T)))
    else
        # TODO: or is it supposed to be the range (-B, B)?
        res = rand(rng, zero(T):(convert(T, B) - one(T)))
    end
    convert(Z, res)
end


function Base.rand(rng::AbstractRNG, ::Type{MLUInt{N, T}}) where {N, T}
    MLUInt{N, T}(tuple((rand(rng, T) for i in 1:N)...))
end


function Base.rand(rng::AbstractRNG, a::MLUInt{N, T}, b::MLUInt{N, T}) where {N, T}
    while true
        res = rand(rng, MLUInt{N, T})
        if res <= b && (a == zero(MLUInt{N, T}) || res >= a)
            return res
        end
    end
end


function _rand_moduint(rng::AbstractRNG, ::Type{Z}, min_val::T, max_val::T) where Z <: AbstractModUInt{T, M} where {T, M}
    # FIXME: this assumes that [min_val, max_val] is close to the full range of T,
    # otherwise rand() will be very slow.
    val = rand(rng, min_val, max_val)
    Z(val, DarkIntegers._verbatim)
end


function Base.rand(rng::AbstractRNG, ::Type{Z}) where Z <: AbstractModUInt{T, M} where {T, M}
    _rand_moduint(rng, Z, zero(T), M - one(T))
end


function rand_nonzero(rng::AbstractRNG, ::Type{Z}) where Z <: AbstractModUInt{T, M} where {T, M}
    _rand_moduint(rng, Z, one(T), M - one(T))
end


function rand_point(rng::AbstractRNG, ::Type{G}) where G <: EllipticCurvePoint{C, Z} where {C, Z <: AbstractModUInt}
    res = rand(rng, Z)
    one(G) * res + one(G)
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
