double(x) = x + x
triple(x) = double(x) + x
square(x) = x * x
cube(x) = square(x) * x


abstract type EllipticCurve end


abstract type EllipticCurvePoint{C, T} end


curve_base(::Type{C}, ::Type{T}) where {C <: EllipticCurve, T} = convert.(T, curve_base(C))
curve_coeff_a(::Type{C}, ::Type{T}) where {C <: EllipticCurve, T} = convert(T, curve_coeff_a(C))
curve_coeff_b(::Type{C}, ::Type{T}) where {C <: EllipticCurve, T} = convert(T, curve_coeff_b(C))


function curve_scalar_type(
        ::Type{C}, ::Type{B}, ::Type{T}) where {C <: EllipticCurve, B <: AbstractModUInt, T <: Unsigned}
    @assert bitsizeof(T) >= num_bits(curve_modulus(C))
    B{T, convert(T, curve_modulus(C))}
end


struct AffinePoint{C <: EllipticCurve, T <: Number} <: EllipticCurvePoint{C, T}
    x :: T
    y :: T
    inf :: Bool

    AffinePoint{C, T}(x::T, y::T) where {C, T} = new{C, T}(x, y, false)
    AffinePoint{C, T}() where {C, T} = new{C, T}(zero(T), zero(T), true)
end


Base.zero(::Type{AffinePoint{C, T}}) where {C, T} = AffinePoint{C, T}()


Base.iszero(p::AffinePoint{C, T}) where {C, T} = p.inf


function Base.one(::Type{AffinePoint{C, T}}) where {C, T}
    bx, by = curve_base(C, T)
    AffinePoint{C, T}(bx, by)
end


function Base.:-(p::AffinePoint{C, T}) where {C, T}
    if iszero(p)
        p
    else
        AffinePoint{C, T}(p.x, -p.y)
    end
end


function Base.:+(p::AffinePoint{C, T}, q::AffinePoint{C, T}) where {C, T}
    if iszero(p)
        return q
    end

    if iszero(q)
        return p
    end

    if p.x == q.x && (p.y != q.y || p.y == 0)
        return zero(AffinePoint{C, T})
    elseif p.x != q.x
        l = (q.y - p.y) * inv(q.x - p.x)
    else
        t = p.x^2
        l = (triple(t) + curve_coeff_a(C, T)) * inv(p.y + p.y)
    end
    x = l^2 - p.x - q.x
    y = l * (p.x - x) - p.y
    AffinePoint{C, T}(x, y)
end


struct JacobianPoint{C <: EllipticCurve, T <: Number} <: EllipticCurvePoint{C, T}
    x :: T
    y :: T
    z :: T
    inf :: Bool

    JacobianPoint{C, T}(x::T, y::T, z::T) where {C, T} = new{C, T}(x, y, z, false)
    JacobianPoint{C, T}(x::T, y::T) where {C, T} = new{C, T}(x, y, one(T), false)
    JacobianPoint{C, T}() where {C, T} = new{C, T}(one(T), one(T), zero(T), true)
end


function Base.:(==)(p::JacobianPoint{C, T}, q::JacobianPoint{C, T}) where {C, T}
    if iszero(p)
        return iszero(q)
    elseif iszero(q)
        return false
    end

    p_z_squared = p.z^2
    q_z_squared = q.z^2
    if p.x * q_z_squared != q.x * p_z_squared
        return false
    end

    p_z_cubed = p_z_squared * p.z
    q_z_cubed = q_z_squared * q.z
    p.y * q_z_cubed == q.y * p_z_cubed
end


Base.convert(::Type{JacobianPoint{C, T}}, p::AffinePoint{C, T}) where {C, T} =
    JacobianPoint{C, T}(p.x, p.y)


Base.zero(::Type{JacobianPoint{C, T}}) where {C, T} = JacobianPoint{C, T}()


Base.iszero(p::JacobianPoint{C, T}) where {C, T} = p.inf


function Base.one(::Type{JacobianPoint{C, T}}) where {C, T}
    bx, by = curve_base(C, T)
    JacobianPoint{C, T}(bx, by)
end


function Base.:-(p::JacobianPoint{C, T}) where {C, T}
    if iszero(p)
        p
    else
        JacobianPoint{C, T}(p.x, -p.y, p.z)
    end
end


function double(p::JacobianPoint{C, T}) where {C, T}

    if iszero(p)
        return p
    end

    a = curve_coeff_a(C)

    XX = square(p.x)
    YY = square(p.y)
    YYYY = square(YY)
    ZZ = square(p.z)
    S = double(square(p.x + YY) - XX - YYYY)
    M = triple(XX)
    if !iszero(a)
        M += convert(T, a) * square(ZZ)
    end
    T_ = square(M) - double(S)
    X3 = T_
    Y3 = M * (S - T_) - double(double(double(YYYY)))
    Z3 = square(p.y + p.z) - YY - ZZ

    JacobianPoint{C, T}(X3, Y3, Z3)
end


function Base.:+(p::JacobianPoint{C, T}, q::JacobianPoint{C, T}) where {C, T}
    if iszero(p)
        return q
    end

    if iszero(q)
        return p
    end

    X1, Y1, Z1 = p.x, p.y, p.z
    X2, Y2, Z2 = q.x, q.y, q.z

    Z1Z1 = square(Z1)
    Z2Z2 = square(Z2)
    U1 = X1 * Z2Z2
    U2 = X2 * Z1Z1
    S1 = Y1 * Z2 * Z2Z2
    S2 = Y2 * Z1 * Z1Z1

    if U1 == U2
        if S1 != S2
            return JacobianPoint{C, T}()
        else
            return double(p)
        end
    end

    H = U2 - U1
    I = square(double(H))
    J = H * I
    r = double(S2 - S1)
    V = U1 * I
    X3 = square(r) - J - double(V)
    Y3 = r * (V - X3) - double(S1 * J)
    Z3 = (square(Z1 + Z2) - Z1Z1 - Z2Z2) * H

    if iszero(Z3)
        JacobianPoint{C, T}()
    else
        JacobianPoint{C, T}(X3, Y3, Z3)
    end
end


struct ChudnovskyPoint{C <: EllipticCurve, T <: Number} <: EllipticCurvePoint{C, T}
    x :: T
    y :: T
    z :: T
    z2 :: T
    z3 :: T
    inf :: Bool

    ChudnovskyPoint{C, T}(x::T, y::T, z::T, z2::T, z3::T) where {C, T} = new{C, T}(x, y, z, z2, z3, false)
    ChudnovskyPoint{C, T}(x::T, y::T) where {C, T} = new{C, T}(x, y, one(T), one(T), one(T), false)
    ChudnovskyPoint{C, T}() where {C, T} = new{C, T}(one(T), one(T), zero(T), zero(T), zero(T), true)
end


Base.convert(::Type{ChudnovskyPoint{C, T}}, p::AffinePoint{C, T}) where {C, T} =
    ChudnovskyPoint{C, T}(p.x, p.y)


function Base.:(==)(p::ChudnovskyPoint{C, T}, q::ChudnovskyPoint{C, T}) where {C, T}
    if iszero(p)
        return iszero(q)
    elseif iszero(q)
        return false
    end

    if p.x * q.z2 != q.x * p.z2
        return false
    end

    p.y * q.z3 == q.y * p.z3
end


Base.zero(::Type{ChudnovskyPoint{C, T}}) where {C, T} = ChudnovskyPoint{C, T}()


Base.iszero(p::ChudnovskyPoint{C, T}) where {C, T} = p.inf


function Base.one(::Type{ChudnovskyPoint{C, T}}) where {C, T}
    bx, by = curve_base(C, T)
    ChudnovskyPoint{C, T}(bx, by)
end


function Base.:-(p::ChudnovskyPoint{C, T}) where {C, T}
    if iszero(p)
        p
    else
        ChudnovskyPoint{C, T}(p.x, -p.y, p.z, p.z2, p.z3)
    end
end


function double(p::ChudnovskyPoint{C, T}) where {C, T}

    if iszero(p)
        return p
    end

    a = curve_coeff_a(C)

    S = double(double(p.x * square(p.y)))
    M = triple(square(p.x))
    if !iszero(a)
        M += convert(T, a) * square(p.z2)
    end
    Xp = square(M) - double(S)
    Yp = M * (S - Xp) - double(double(double(square(square(p.y)))))
    Zp = double(p.y * p.z)
    Zp2 = square(Zp)
    Zp3 = Zp2 * Zp

    ChudnovskyPoint{C, T}(Xp, Yp, Zp, Zp2, Zp3)
end


function Base.:+(p::ChudnovskyPoint{C, T}, q::ChudnovskyPoint{C, T}) where {C, T}
    if iszero(p)
        return q
    end

    if iszero(q)
        return p
    end

    X1, Y1, Z1 = p.x, p.y, p.z
    X2, Y2, Z2 = q.x, q.y, q.z

    U1 = X1 * q.z2
    U2 = X2 * p.z2
    S1 = Y1 * q.z3
    S2 = Y2 * p.z3
    if U1 == U2
        if S1 != S2
            return ChudnovskyPoint{C, T}()
        else
            return double(p)
        end
    end

    H = U2 - U1
    I = square(double(H))
    J = H * I
    r = double(S2 - S1)
    V = U1 * I
    X3 = square(r) - J - double(V)
    Y3 = r * (V - X3) - double(S1 * J)
    Z3 = (square(Z1 + Z2) - p.z2 - q.z2) * H

    Z3_2 = square(Z3)
    Z3_3 = Z3_2 * Z3
    ChudnovskyPoint{C, T}(X3, Y3, Z3, Z3_2, Z3_3)
end


function repeated_double(p, m)
    for i in 1:m
        p = double(p)
    end
    p
end


function mul_double_and_add(p::P, y::V) where {P <: EllipticCurvePoint, V <: Union{Integer, BigInt}}
    if iszero(y)
        zero(P)
    elseif isone(y)
        p
    else
        acc = zero(P)
        while true
            if isodd(y)
                acc += p
            end
            if iszero(y)
                break
            else
                p = double(p)
                y >>= 1
            end
        end
        acc
    end
end


function mul_windowed(p::P, y::V, w::Int=4) where {P <: EllipticCurvePoint, V <: Union{Integer, BigInt}}

    if iszero(y)
        return zero(P)
    elseif isone(y)
        return p
    end

    precomp = Array{P}(undef, 1 << w)
    precomp[1] = p
    for i in 2:(1 << w)
        precomp[i] = p + precomp[i-1]
    end

    nb = num_bits(y)

    acc = zero(P)
    for i in (nb ÷ w):-1:0
        acc = repeated_double(acc, w)
        d = y >> (i * w)
        if !iszero(d)
            acc += precomp[d]
        end
        y = y - (d << (i * w))
    end
    acc
end


function mul_sliding_window(p::P, y::V, w::Int=4) where {P <: EllipticCurvePoint, V <: Union{Integer, BigInt}}

    if iszero(y)
        return zero(P)
    elseif isone(y)
        return p
    end

    precomp = Array{P}(undef, 1 << (w - 1))
    precomp[1] = repeated_double(p, w - 1)
    for i in 2:(1 << (w - 1))
        precomp[i] = p + precomp[i-1]
    end

    nb = num_bits(y)

    acc = zero(P)
    while true
        new_nb = num_bits(y)
        acc = repeated_double(acc, new_nb < w ? nb - w : nb - new_nb)

        if new_nb < w
            return acc + p * y
        end

        t = y >> (new_nb - w)
        acc += precomp[t - (1 << (w - 1) - 1)]

        nb = new_nb
        y = y - (t << (new_nb - w))
    end
    acc
end


function mul_wnaf(p::P, y::V, w::Int=4) where {P <: EllipticCurvePoint, V <: Union{Integer, BigInt}}

    if iszero(y)
        return zero(P)
    elseif isone(y)
        return p
    end

    l = 1 << (w - 1)
    precomp = Array{P}(undef, l) # corresponds to di = [1, 3, 5, ..., 2^(w-1)-1, -2^(w-1)-1, ..., -3, -1]

    dp = double(p)
    precomp[1] = p
    precomp[end] = -p

    for i in 2:(l>>1)
        precomp[i] = precomp[i-1] + dp
        precomp[end-i+1] = -precomp[i]
    end

    ds = Tuple{Int, Int}[]
    i = 0
    while !iszero(y)
        tz = trailing_zeros(y)
        y >>= tz
        i += tz

        di = convert(Int, y & ((1 << w) - 1))
        if di >= 1 << (w - 1)
            y += ((1 << w) - di)
        else
            y -= di
        end
        push!(ds, (i, di))
    end

    acc = zero(P)
    for j in length(ds):-1:1
        i, di = ds[j]
        acc = acc + precomp[(di >> 1) + 1]
        acc = repeated_double(acc, j == 1 ? i : i - ds[j-1][1])
    end

    acc
end


function Base.:*(p::P, y::Union{ModUInt, MgModUInt}) where {P <: EllipticCurvePoint}
    p * value(y)
end


function Base.:*(p::P, y::V) where {P <: EllipticCurvePoint, V <: Union{Integer, BigInt}}
    mul_wnaf(p, y)
end


struct Curve_secp256k1 <: EllipticCurve end

curve_modulus(::Type{Curve_secp256k1}) = big(2)^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
curve_order(::Type{Curve_secp256k1}) = as_builtin(MLUInt{4, UInt64}(reverse((
    0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE, 0xBAAEDCE6AF48A03B, 0xBFD25E8CD0364141))))
curve_base(::Type{Curve_secp256k1}) = (
        as_builtin(MLUInt{4, UInt64}(reverse((
                0x79BE667EF9DCBBAC, 0x55A06295CE870B07, 0x029BFCDB2DCE28D9, 0x59F2815B16F81798)))),
        as_builtin(MLUInt{4, UInt64}(reverse((
                0x483ADA7726A3C465, 0x5DA4FBFC0E1108A8, 0xFD17B448A6855419, 0x9C47D08FFB10D4B8)))))
curve_coeff_a(::Type{Curve_secp256k1}) = 0
curve_coeff_b(::Type{Curve_secp256k1}) = 7
