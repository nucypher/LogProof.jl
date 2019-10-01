const q = UInt64(251)
const Zq = RRElem{UInt64, q}

const p = secp256k1_order # 0xffffffff00000001
const Zp = RRElem{secp256k1_base_type, p} # RRElem{UInt64, p}

# in the centered representation the range of Z* is [-half_mod, half_mod]
half_mod(::Type{Zq}) = convert(Zq, q >> 1)
half_mod(::Type{Zp}) = convert(Zp, p >> 1)

#const G = Zp
const G = Point{secp256k1_type}
const G_lazy = LazyPoint{secp256k1_type, Zp}

const Rq = Polynomial{Zq}
const d = 8
const f_norm = 1 # maximum absolute value of all of coefficients of `f`

# Polynomial x^d + 1 for use in find_residuals()
const f_exp = Polynomial(convert.(Zp, vcat([1], zeros(Int, d-1), [1], zeros(Int, d-1))), true,
    DarkIntegers.karatsuba_mul)


function rand_Zq(rng, B::Int=0)
    tp = encompassing_type(Zq)
    if B == 0
        res = rand(rng, zero(tp):(convert(tp, q) - one(tp)))
    else
        res = rand(rng, zero(tp):(convert(tp, B) - one(tp)))
    end
    convert(Zq, res)
end


function rand_Zq_polynomial(rng::AbstractRNG, B::Int=0)
    Polynomial([rand_Zq(rng, B) for i in 1:d], true, DarkIntegers.karatsuba_mul)
end


function rand_mp(rng, ::Type{MPNumber{N, T}}) where {N, T}
    MPNumber{N, T}(tuple((rand(rng, T) for i in 1:N)...))
end


function rand_mp(rng, a::MPNumber{N, T}, b::MPNumber{N, T}) where {N, T}
    while true
        res = rand_mp(rng, MPNumber{N, T})
        if res <= b && (a == zero(MPNumber{N, T}) || res >= a)
            return res
        end
    end
end


function rand_Zp(rng, min_val::RRElemMontgomery{T, M}, max_val::RRElemMontgomery{T, M}) where {T, M}
    RRElemMontgomery{T, M}(rand_mp(rng, min_val.value, max_val.value), DarkIntegers._no_modulo)
end


function rand_Zp(rng)
    tp = DarkIntegers.rr_base_type(Zp)
    m = DarkIntegers.rr_modulus(Zp)
    Zp(rand_mp(rng, zero(tp), m - one(tp)), DarkIntegers._verbatim)
end


function rand_Zp_nonzero(rng)
    tp = DarkIntegers.rr_base_type(Zp)
    m = DarkIntegers.rr_modulus(Zp)
    Zp(rand_mp(rng, one(tp), m - one(tp)), DarkIntegers._verbatim)
end


function rand_G(rng)
    tp = DarkIntegers.rr_base_type(secp256k1_type)
    res = Zp(rand_mp(rng, one(tp), p), DarkIntegers._verbatim)
    #secp256k1_base^res
    instantiate(LazyPoint(secp256k1_curve, res))
end


# Convert a polynomial on a ring to a polynomial with coefficients in Z and double length
# (so that multiplication result fit in)
function expand(p::Rq)
    change_length(2 * length(p.coeffs), Polynomial(convert.(Zp, p.coeffs), p.negacyclic, DarkIntegers.karatsuba_mul))
end


# returns the degree of the polynomial
# (index of the maximum power of X with nonzero coefficient minus 1)
function polynomial_degree(p::Polynomial{T}) where T
    res = findlast(x -> x != zero(T), p.coeffs)
    if !(res === nothing)
        res - 1
    else
        -1
    end
end


function Base.divrem(p::Polynomial, f::Polynomial)

    r = copy(p)
    r.coeffs .= 0

    f_deg = polynomial_degree(f)

    while true
        p_deg = polynomial_degree(p)

        if f_deg > p_deg
            return r, p
        end

        # TODO: assuming here that there is no remainder
        c = p.coeffs[p_deg + 1] ÷ f.coeffs[f_deg + 1]

        p -= shift_polynomial(f, p_deg - f_deg) * c
        r.coeffs[p_deg - f_deg + 1] = c
    end
end


function apply(p::Polynomial{T}, alpha::T) where T
    sum(p.coeffs .* alpha .^ (0:length(p.coeffs)-1))
end


Base.copy(p::Polynomial) = Polynomial(copy(p.coeffs), p.negacyclic)


"""
Convert a number `z in [2^(b-1), 2^(b-1))` to its binary representation such that
`z = z_0 + z_1 * 2 + z_2 * 2^2 + ... + z_{b-2} * 2^(b-2) - z_{b-1} * 2^(b-1)`
"""
function binary(val::T, b::Int) where T <: Union{Zq, Zp}
    # Note that we're getting numbers in Zq or Zp, (with possibly 2^b>q)
    # but the resulting contract must be valid in Zp
    # TODO: performance can be improved
    is_negative = val > half_mod(T)
    if is_negative
        val += 1 << (b-1) # adding an offset and treating it as a positive number
    end
    x = DarkIntegers.rr_value(val)
    res = Array{Bool, 1}(undef, b)
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


function powers_of_2(::Type{T}, d) where T
    res = convert(T, 2) .^ (0:d-1)
    res[end] = -res[end] # TODO: check if it works as intended
    res
end
