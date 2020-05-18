@testgroup "Encryption" begin


@testcase "Encrypt/decrypt" for rng in fixed_rng(123)

    params = EncryptionParams(8191, 4, 2, 16)

    skey = SecretKey(rng, params)
    pkey = PublicKey(rng, skey)

    m = rand_message(rng, params)

    pk, ct = encrypt(rng, pkey, m)
    m_back = decrypt(skey, ct)

    @test m == m_back
end


end
