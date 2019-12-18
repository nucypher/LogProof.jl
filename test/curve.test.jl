@testgroup "Curve" begin


@testcase "SECP256k1" begin

    # Basically the same SECP256k1 curve defined in `curve.jl`,
    # but using `MLUInt{8, UInt32}` as the base type

    ml_tp = MLUInt{8, UInt32}
    m = zero(ml_tp) - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1

    tp = ModUInt{MLUInt{8, UInt32}, m}

    a = zero(tp)
    b = convert(tp, 7)
    params = LogProof.CurveParams{tp}(a, b)

    base = LogProof.Point{tp}(
        params,
        ml_tp(reverse((
            0x79BE667E, 0xF9DCBBAC, 0x55A06295, 0xCE870B07,
            0x029BFCDB, 0x2DCE28D9, 0x59F2815B, 0x16F81798))),
        ml_tp(reverse((
            0x483ADA77, 0x26A3C465, 0x5DA4FBFC, 0x0E1108A8,
            0xFD17B448, 0xA6855419, 0x9C47D08F, 0xFB10D4B8))))
    order = ml_tp(reverse((
        0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFE,
        0xBAAEDCE6, 0xAF48A03B, 0xBFD25E8C, 0xD0364141)))

    order_bi = as_builtin(order)

    @test (base^(order_bi - 1) * base).inf
    @test (base^order_bi).inf
    @test base^(order_bi + 1) == base
end


end
