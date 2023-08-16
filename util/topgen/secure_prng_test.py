#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest

import secure_prng as sp
import secrets

# CTR_DRBG test vectors.
#
# Test vectors sourced from NIST's website:
# https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators#DRBG
#
# Test vector: CTR_DRBG AES-128 no DF.
# [AES-128 no df]
# [PredictionResistance = False]
# [EntropyInputLen = 256]
# [NonceLen = 0]
# [PersonalizationStringLen = 0]
# [AdditionalInputLen = 0]
# [ReturnedBitsLen = 512]


vectors = [
    {
        'EntropyInput': '0xce50f33da5d4c1d3d4004eb35244b7f2'
                        'cd7f2e5076fbf6780a7ff634b249a5fc',
        'Key_Inst': '0x96b20ff35faaf1b2e27f53e4f6a3f2a8',
        'V_Inst': '0xcef7f49e164d55eaf957348dc3fb5b84',
        'Key_First': '0x2e8bf07c5a29b97633576a7c4d5343dd',
        'V_First': '0x3f93dbc9dc724d654f5f2a45b818c7ec',
        'ReturnedBits': '0x6545c0529d372443b392ceb3ae3a99a3'
                        '0f963eaf313280f1d1a1e87f9db373d3'
                        '61e75d18018266499cccd64d9bbb8de0'
                        '185f213383080faddec46bae1f784e5a',
        'Key_Second': '0xa103e1669b0641cae87caab70a741bf1',
        'V_Second': '0xfbe9d7c15217c737b408e31679170140'
    },
    {
        'EntropyInput': '0xa385f70a4d450321dfd18d8379ef8e77'
                        '36fee5fbf0a0aea53b76696094e8aa93',
        'Key_Inst': '0xfb670bc4b73b3340e9ae90d4dd08cb2d',
        'V_Inst': '0x35763f3590160d37c85eabd9e55a54eb',
        'Key_First': '0xee2290a1d5db30d782d72beed9ae3569',
        'V_First': '0x4be72a395e7cc8a603d8b86e28c2ba13',
        'ReturnedBits': '0x1a062553ab60457ed1f1c52f5aca5a3b'
                        'e564a27545358c112ed92c6eae2cb759'
                        '7cfcc2e0a5dd81c5bfecc941da5e8152'
                        'a9010d4845170734676c8c1b6b3073a5',
        'Key_Second': '0x062eb030e66974d87ef04566e09b2f45',
        'V_Second': '0x262084c8600eb42ee7ebc11f57f46a5b'
    },
    {
        'EntropyInput': '0xd4f47c385e5ee36915978386a074d413'
                        'd04a1ce3a13a0fe2b17f3f20f83a93fd',
        'Key_Inst': '0x8c1680f6a420d30823e89ed104939149',
        'V_Inst': '0xd3c2c62dc18cac704257fd9989886d85',
        'Key_First': '0xe9f6401c4543a1ab655b9d8bc7fc201b',
        'V_First': '0xf0575cc3fc5052739b652755bc1f9c17',
        'ReturnedBits': '0x27f880df4c2907697fb2f594e311559c'
                        'ea827049327af31fa7f0cbf332c46206'
                        '74f503d7dc378320d228907151d32ee5'
                        'e3f5c5eccb13afe58bf6a60192e6d70e',
        'Key_Second': '0xf9fbd08bbe7d6cce3ef7ccf1e8871565',
        'V_Second': '0x1896fa321389cd720bf9af48595c27e3'
    },
    {
        'EntropyInput': '0x123dd82c6a8d6a5f23067702e8222733'
                        'a39c48965baccd9bffed5dc51cb789b6',
        'Key_Inst': '0x4adf24e290f35a3e15796a554cc56269',
        'V_Inst': '0xa01492583b1a6e090cc59f7c6d0577ce',
        'Key_First': '0x2455db0e422e1ff380faf65dd413f9e7',
        'V_First': '0xb8a8c6ffc9e4c3be925a94a421ab47c9',
        'ReturnedBits': '0x12dd6a874a4656c7d5a21cb1179b3c4a'
                        '9982ae00fc1bf26cb3a139cb21c45050'
                        '45ff5e223e2d081fee52b22246d485b9'
                        'f1274aef79a3301d2636999799aad31d',
        'Key_Second': '0x8e79c575e7de9ca9fc23447569d43395',
        'V_Second': '0xc3be4b595794eb411f131f20144ab206'
    },
    {
        'EntropyInput': '0xf1a69af890b2c979fae046a2b58d00a8'
                        '331c5322472b0e619bb372bfd027f705',
        'Key_Inst': '0xa94466366accf918cc9f5bf5116a45f2',
        'V_Inst': '0x309489ec279dadf3689bb006a195097d',
        'Key_First': '0x1a7c19663ab5ae9991234bb9a00358ea',
        'V_First': '0x6ac9a2238a3ed9da84f70945159a3401',
        'ReturnedBits': '0x96091258c4224e3b03d65c938c97832b'
                        '55143069db5755196d52f525be959d51'
                        '9b1e02e5f2dabf4dd2164f9bb06a16a6'
                        '3576ff6deb042dab74033916c95498c1',
        'Key_Second': '0xae91573399f81e208840841701ff743e',
        'V_Second': '0x6e8d009a73c3eade9eeaa5b0262d9f51'
    },
    {
        'EntropyInput': '0x14a9a1e20ca3686f3ec09603f6730bdd'
                        '73a9cc8c32388ec00bc28e6c9ec65d87',
        'Key_Inst': '0x4c4b5d2cf6dd580e08bf8b5452944e87',
        'V_Inst': '0x70211642528e2d52f8ea4cd5ef74a3ff',
        'Key_First': '0x804b3b0d3d7a83bda3700f5dfc34041c',
        'V_First': '0x4fdaf404e9e669c78263df43410bf80a',
        'ReturnedBits': '0xc12946457ad89dde788e13c5092bbf3e'
                        '9c7f61eac73261d01d396a1d9d1163ee'
                        'e847a561d8e52080cd9bdce570141782'
                        'ebf167c4700a66aca6fd5c9116a7be49',
        'Key_Second': '0x5aa43bd012bcb092e7b39c9427af2b7f',
        'V_Second': '0xe54c4cf6d443b47862923c435148c17b'
    },
    {
        'EntropyInput': '0x97261a2c19c6dc36a6d0283a177eb966'
                        '6c21817fc0fca462c53d90b3d814cd92',
        'Key_Inst': '0xcfc4e6e2e3b8ec5790af356db399fc3c',
        'V_Inst': '0x6fa95bb1a04a07f03615520aa9a633ea',
        'Key_First': '0x555e537484452f1ddce6c72d3eaa1c58',
        'V_First': '0x9d0e04c9f3dc12dd046fddd0d90c6ec8',
        'ReturnedBits': '0xb474f2743b6182b051fc7c76c6b4085b'
                        '2f597639ca19c1eee05c1cf439bb8edb'
                        'e093d0b2239de5d0f79bebf0e622fe04'
                        'b513597ed1d8a02821a0bca435d1fbde',
        'Key_Second': '0x830ee554a8157012de1158018d4687b2',
        'V_Second': '0x42d9e8ae414a2ea618d04d7d6c16f172'
    },
    {
        'EntropyInput': '0x9fdde0f7eba65381bf637d7b7e6fbc20'
                        'deef906013018655f8d12d747db8e225',
        'Key_Inst': '0xc73f1c3911d863e0891c602cda88f97a',
        'V_Inst': '0xdd674aae73b725c70bf9efcd0c0a1c5d',
        'Key_First': '0xa0b8e12ad04956a37c3403f5b99ad4ac',
        'V_First': '0xa2f2fb15a045b57aee7505a51eb1e1e7',
        'ReturnedBits': '0xf4a55aa4c245cd42a1b6429637b07741'
                        '89ef4e5053bef06bbf422b2f10399e18'
                        'b9f86dcc56aaa6975ea15622cdebf36a'
                        '3f4778447bb23a2044c283a79903beac',
        'Key_Second': '0x8f3146955550f436a4e99c0b47ec278c',
        'V_Second': '0x19e6faecddfe76a623bea364ba698b93'
    },
    {
        'EntropyInput': '0xaf62299f37895332d283ff9f3b0ca29f'
                        '9003571893ddd1bc2d28633a33992b4a',
        'Key_Inst': '0xf780d551cdf76353e4fce2c89febe7c5',
        'V_Inst': '0x938b8dd6f36b722ede00a183422bd532',
        'Key_First': '0x8b645bd924fd6ef1b113abd9aab5a775',
        'V_First': '0x61202af05a27e1969cd2e2543d137b59',
        'ReturnedBits': '0xb91719f2d1297fa9c51720ab9448228e'
                        '333594a7a1c0a5d7a10ae88249dc0cc5'
                        'd07abe20b7915d2a87f12ec4bcdf44ef'
                        'a911f28c5e9e3909018e4a6bd1b5363b',
        'Key_Second': '0xd82b481ecbb5131265cdf0e8b6e7482f',
        'V_Second': '0x0bd2e03cb59d42ed4419af0620bf0c7f'
    },
    {
        'EntropyInput': '0x42fe0ad088d5c1d6be9e02c147d5770c'
                        '9aa0a977c6300cd9aec940cd15ecfb8d',
        'Key_Inst': '0x1a1cf61e72abf1b788e11f96e3323256',
        'V_Inst': '0x992873b9a686af4b5de18274645e05f5',
        'Key_First': '0x4c34e93bc7cf55f83416fedcd7a23ac2',
        'V_First': '0x0cd82da25c101cbbdd64d6919a226bfd',
        'ReturnedBits': '0xbd1a65bb65b55ec4d6279cb94dbf3bcd'
                        '82bce09fa277bfea50b5dab64b06c018'
                        '1570032a3a6f7dee5b2ccea34bc6928d'
                        'b11dec9329ed90d109c0bcca7ce7a428',
        'Key_Second': '0xb5d6e7668fb2e810c7e8029165689852',
        'V_Second': '0x9432a85d32c78fde648c82c21ce57ce8'
    },
    {
        'EntropyInput': '0x744ed74d83bacf92d4bd4dd052458bd8'
                        'af10391c66fc89e13974426320aa474a',
        'Key_Inst': '0x2cac2b8379c4fff3e2c25087f6a2ce82',
        'V_Inst': '0xac98e3d2064a2a73ca5c80da5118b932',
        'Key_First': '0x98d047114511e218f86a7835cc71be8c',
        'V_First': '0xaee6486c59d2014531872f5ef7bad59d',
        'ReturnedBits': '0x8ddd0270b07fbbd339bc83ea7a1d986e'
                        'e8e1a061c7e31c5dbdccabc8f2522783'
                        '2ec45f5ef9f28ca0446d844daadd1920'
                        '24c4d36854fa23b58a8b9794db6d3acb',
        'Key_Second': '0x0c264efe483527712a381bfc8284f536',
        'V_Second': '0xde8dcadb69a4d198335e5553d3cfd6f7'
    },
    {
        'EntropyInput': '0x884e9faa661dcecc3765c797a2af8906'
                        'fb893813a396e02b94993826288d2a6d',
        'Key_Inst': '0xd0ac63649c63fead011adac00648cc5c',
        'V_Inst': '0xf801e2ddc32043b967b1fa9f593fd415',
        'Key_First': '0x4f2d3c527262cbd2422305adbdd3ecb5',
        'V_First': '0x1d4991743d6a01de237f7ddbc9145618',
        'ReturnedBits': '0x18481dc45ca3f1896fe6394a2367d44c'
                        '4e458b455c9f36a5d5ac2b6a7475cf75'
                        '99a9378f9cc72ffcdbea71f09c9a244a'
                        '36cd660b722546ea2af4f3e77596ec25',
        'Key_Second': '0x26614d22956a94c8536711b1c388ad98',
        'V_Second': '0x66dc871cc3dcefd46915467a9caa6b82'
    },
    {
        'EntropyInput': '0x31d108fe0d40fe05c9ed8372c3bc09d1'
                        '058b397b9006fb373cdd16a5a40e2cc1',
        'Key_Inst': '0x6933f430f73ece64ff929e25675b4c8b',
        'V_Inst': '0x0603e3b5f0b058a5cff5d41cd5bcd2b9',
        'Key_First': '0x3ae1454d588f9bc295edd4d3c868314b',
        'V_First': '0x141fc05a219875c793186ef90676ac02',
        'ReturnedBits': '0x80822450b0487e70ada948da0b25cc49'
                        'a37dc58e0dad9233badd0e88df520d36'
                        '54300f081b02e8545d6d6818b82e4596'
                        '4db8633fc769af84a9799e92a1bb0d61',
        'Key_Second': '0x74430ba978923430c5353dcc34724662',
        'V_Second': '0x726943d9dedfad44d2825c76b504e0c4'
    },
    {
        'EntropyInput': '0xd5464a18aab8873d63f572f6738ef27a'
                        '39845a31a211700310321e42b6620b4a',
        'Key_Inst': '0x8da4b6d650c6b75c558a6fa1d769b720',
        'V_Inst': '0x3a0c80ffc2a7d391e31adcfbc7d0f532',
        'Key_First': '0x8b7ac3a53685a0ee321833055a378e3d',
        'V_First': '0xd31c64982a2efc79e480a3d594c500f9',
        'ReturnedBits': '0xe2b531ea43c513a1564fa65e9a68d43c'
                        '875137773102941d0ef544c84e3689b8'
                        '2eac32d8e29cce42eae393e086ab81f7'
                        '0520179288c52cbb6448699723865b49',
        'Key_Second': '0xac29469fae430f14a9b61c4f9064e40d',
        'V_Second': '0xac9c77c6f857dd3e38bf0f54a8652ad0'
    },
    {
        'EntropyInput': '0x727c0ac75a99bb1a318e4fe2fe0f2e31'
                        '2b3b61d82b2e5071acfb4a36bc8258c1',
        'Key_Inst': '0x2a9ef609a0e78b7b07f152b55ae86b6b',
        'V_Inst': '0x28b3bb164b98f3e35fd3888fcd30a6b9',
        'Key_First': '0xa2e4be0b0bd0aac58afeceff8790db51',
        'V_First': '0x39e906711699b1a66d42cfbd68aa5571',
        'ReturnedBits': '0xf595ee1af437fe1bed8d451088b788f1'
                        'cd599f2b0c47feac1fb5c6efbf7a14a8'
                        'ab0ea11a3569a3c23b2a9702b415bda3'
                        '55c15afd275c0d67b38bcfb54ab13f70',
        'Key_Second': '0xa90d63f8844c34461cb53c313e4a165c',
        'V_Second': '0xe10a03b98d8a61df19739af42ae085b9'
    },
]


class TestNistOfficial(unittest.TestCase):

    def test_compare(self):
        """Ensure that known seeds generate the expected results."""
        for test_point in vectors:
            # Read the entropy input from the test point
            entropy_input = int(test_point['EntropyInput'], 16)
            # Receive results from secure_prng.py
            received = sp.test_point_gen(entropy_input)
            self.assertEqual(test_point, received)

    def test_getrandbits(self):
        """
        Test secure_random.getrandbits() using test vectors

        Reseed PRNG using entropy_input.
        Use sp.getrandbits to forward the generator to a randomly selected byte
        of ReturnedBits, and to fetch randomly selected number of bits.
        """
        # Randomly select a testpoint from 15 available vectors.
        test_point = vectors[secrets.randbelow(15)]
        # Randomly select a section of ReturnedBits
        offset = 8 * secrets.randbelow(32)
        width = secrets.randbelow(256)
        # Compute expected result from a testpoint
        ReturnedBits = int(test_point['ReturnedBits'], 16)
        expected = (ReturnedBits % (1 << (512 - offset))) >> (512 - width - offset)

        # Re-seed secure_prng with the EntropyInput from the test_point
        entropy_input = int(test_point['EntropyInput'], 16)
        sp.reseed(entropy_input)
        # Call getrandbits function
        sp.getrandbits(512)
        sp.getrandbits(offset)
        received = sp.getrandbits(width)

        # compare results
        self.assertEqual(expected, received)


class TestIdempotence(unittest.TestCase):

    def test_idempotence(self):
        """Ensure that the same seed produces the same result"""
        outputs = list()
        seed = secrets.randbits(256)
        for i in range(10):
            sp.reseed(seed)
            outputs.append(sp.getrandbits(1024))
        self.assertTrue(len(set(outputs)) == 1)


if __name__ == '__main__':
    unittest.main()
