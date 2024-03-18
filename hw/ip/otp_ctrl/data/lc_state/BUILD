# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "otp_json",
    "otp_partition",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_raw",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 0,
            state = "RAW",
        ),
    ],
    seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
)

[
    otp_json(
        name = "otp_json_test_unlocked{}".format(i),
        partitions = [
            otp_partition(
                name = "LIFE_CYCLE",
                count = (i * 2) + 1,
                state = "TEST_UNLOCKED{}".format(i),
            ),
        ],
        seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
    )
    for i in range(0, 8)
]

[
    otp_json(
        name = "otp_json_test_locked{}".format(i),
        partitions = [
            otp_partition(
                name = "LIFE_CYCLE",
                count = (i + 1) * 2,
                state = "TEST_LOCKED{}".format(i),
            ),
        ],
        seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
    )
    for i in range(0, 7)
]

otp_json(
    name = "otp_json_dev",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = "5",
            state = "DEV",
        ),
    ],
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
)

otp_json(
    name = "otp_json_prod",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 5,
            state = "PROD",
        ),
    ],
    seed = "113517944176559405110937879233240229311794601727326023435899657066678782830485",
)

otp_json(
    name = "otp_json_prod_end",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 5,
            state = "PROD_END",
        ),
    ],
    seed = "113517944176559405110937879233240229311794601727326023435899657066678782830485",
)

otp_json(
    name = "otp_json_rma",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 8,
            state = "RMA",
        ),
    ],
    seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
)
