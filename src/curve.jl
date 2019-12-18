using DarkIntegers


struct CurveParams{T <: Number}
    a :: T
    b :: T
end


struct Point{T <: Number} <: Number
    params :: CurveParams{T}
    x :: T
    y :: T
    inf :: Bool

    Point{T}(params, x, y) where T = new{T}(params, x, y, false)
    Point{T}(params) where T = new{T}(params, zero(T), zero(T), true)
end


Base.one(::Type{Point{T}}) where T = Point{T}(CurveParams{T}(zero(T), zero(T)))

Base.:^(x::Point{T}, y::Bool) where T = y ? x : one(Point{T})


Base.show(io::IO, p::Point) = print(io, "P($(as_builtin(value(p.x))), $(as_builtin(value(p.y))))")


struct Curve{T <: Number}
    params :: CurveParams{T}
    base_point :: Point{T}
end


struct LazyPoint{T, V} <: Number
    curve :: Curve{T}
    power :: V
end


function Base.:^(x::LazyPoint{T, V}, y::Union{Integer, BigInt}) where {T, V}
    LazyPoint{T, V}(x.curve, x.power * convert(V, y))
end


function instantiate(x::LazyPoint{T, V}) where {T, V}

    @assert !iszero(x.power)

    y = value(x.power)

    tz = trailing_zeros(y)
    res = secp256k1_powers[tz + 1]
    pwr = tz + 2
    y >>= tz + 1
    while !iszero(y)
        if isodd(y)
            res *= secp256k1_powers[pwr]
        end
        y >>= 1
        pwr += 1
    end

    res

end


function Base.:*(x::Point{T}, y::LazyPoint{T, V}) where {T, V}
    x * instantiate(y)
end

function Base.:*(x::LazyPoint{T, V}, y::Point{T}) where {T, V}
    y * x
end

function Base.:*(x::LazyPoint{T, V}, y::LazyPoint{T, V}) where {T, V}
    LazyPoint{T, V}(x.curve, x.power + y.power)
end


function Base.:^(x::Point, y::ModUInt)
    x^value(y)
end

function Base.:^(x::Point, y::MgModUInt)
    x^value(y)
end


function Base.:*(p::Point{T}, q::Point{T}) where T
    #@assert p.params == q.params
    if !iszero(p.params.a) && !iszero(p.params.b)
        params = p.params
    else
        params = q.params
    end

    if p.inf
        return q
    end

    if q.inf
        return p
    end

    if p.x == q.x && (p.y != q.y || p.y == 0)
        return Point{T}(params)
    elseif p.x != q.x
        l = (q.y - p.y) * inv(q.x - p.x)
    else
        t = p.x^2
        l = (t + t + t + params.a) * inv(p.y + p.y)
    end
    x = l^2 - p.x - q.x
    y = l * (p.x - x) - p.y
    Point{T}(params, x, y)
end


const secp256k1_base_type = MLUInt{4, UInt64}
const secp256k1_modulus = zero(secp256k1_base_type) - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
const secp256k1_order = MLUInt{4, UInt64}(reverse((
            0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE,
            0xBAAEDCE6AF48A03B, 0xBFD25E8CD0364141)))
const secp256k1_type = ModUInt{secp256k1_base_type, secp256k1_modulus}
const secp256k1 = CurveParams{secp256k1_type}(zero(secp256k1_type), convert(secp256k1_type, 7))
const secp256k1_base = Point{secp256k1_type}(
            secp256k1,
            secp256k1_base_type(reverse((
                0x79BE667EF9DCBBAC, 0x55A06295CE870B07,
                0x029BFCDB2DCE28D9, 0x59F2815B16F81798))),
            secp256k1_base_type(reverse((
                0x483ADA7726A3C465, 0x5DA4FBFC0E1108A8,
                0xFD17B448A6855419, 0x9C47D08FFB10D4B8))))

const secp256k1_curve = Curve(secp256k1, secp256k1_base)


function get_secp256k1_powers()
    res = Array{Point{secp256k1_type}, 1}(undef, 256)
    res[1] = secp256k1_base
    for i in 2:256
        res[i] = res[i-1] * res[i-1]
    end
    res
end


const secp256k1_powers = get_secp256k1_powers()
