using DarkIntegers
using BenchmarkTools

using LogProof:
    Curve_secp256k1, curve_scalar_type, AffinePoint, JacobianPoint, ChudnovskyPoint,
    curve_order, double


function benchmark_result(trial)
    time_str = BenchmarkTools.prettytime(minimum(trial.times))

    if trial.allocs > 0
        mem_str = BenchmarkTools.prettymemory(trial.memory)
        alloc_str = ", $mem_str ($(trial.allocs) allocs)"
    else
        alloc_str = ""
    end

    time_str * alloc_str
end


function ref_mul(p, y)
    res = p
    for i in 2:y
        res += p
    end
    res
end


@testgroup "Curve" begin


point_types = [AffinePoint, JacobianPoint, ChudnovskyPoint] => ["affine", "Jacobian", "Chudnovsky"]


@testcase "SECP256k1" for point_type in point_types

    stp = curve_scalar_type(Curve_secp256k1, MgModUInt, MLUInt{4, UInt64})
    ref_ptp = AffinePoint{Curve_secp256k1, stp}
    ptp = point_type{Curve_secp256k1, stp}
    order = curve_order(Curve_secp256k1)

    b = one(ptp)
    b_ref = one(ref_ptp)

    # Trivial tests for point_type == AffinePoint
    @test double(b) == convert(ptp, double(b_ref))
    @test b + b == convert(ptp, b_ref + b_ref)
    @test double(b) + b == convert(ptp, double(b_ref) + b_ref)

    @test ref_mul(b + b, 23) == (b + b) * 23
    @test iszero(b * (order - 1) + b)
    @test iszero(b * order)
    @test b * (order + 1) == b
end


@testcase "SECP256k1, addition performance" for point_type in point_types

    stp = curve_scalar_type(Curve_secp256k1, MgModUInt, MLUInt{4, UInt64})
    ptp = point_type{Curve_secp256k1, stp}

    b1 = one(ptp)
    b2 = double(b1)
    b4 = double(b2)

    trial = @benchmark $b2 + $b4
    @test_result benchmark_result(trial)
end


@testcase "SECP256k1, multiplication performance" for point_type in point_types

    stp = curve_scalar_type(Curve_secp256k1, MgModUInt, MLUInt{4, UInt64})
    ptp = point_type{Curve_secp256k1, stp}

    b1 = one(ptp)
    b2 = double(b1)

    trial = @benchmark $b2 * 1234567
    @test_result benchmark_result(trial)
end


end
