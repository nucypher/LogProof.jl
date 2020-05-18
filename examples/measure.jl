using Profile
using LogProof
using Random
using DarkIntegers
using DarkCurves
using Curve25519


function test_run(warmup=false)

    rng = MersenneTwister(123)

    params = EncryptionParams(8191, 4, 2, 1024, RistrettoCurveVT)

    skey = SecretKey(rng, params)
    pkey = PublicKey(rng, skey)

    m = rand_message(rng, params)

    if !warmup
        LogProof.reset_stage_timer!()
    end
    pk, ct = encrypt(rng, pkey, m)
    main_synchronous(rng, pk, pk.verifier_knowledge)
    m_back = decrypt(skey, ct)
    if !warmup
        LogProof.display_stage_timer()
    end


    @assert m == m_back
end


function main()

    println("warm-up starting")
    test_run(true)
    println("warm-up done")
    println()

    test_run()
end


main()
