// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

extern "C" {
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
}

#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"

namespace perso_tlv_data_fuzztest {
namespace {

using ::fuzztest::Arbitrary;
using ::fuzztest::ArrayOf;
using ::fuzztest::ElementOf;
using ::fuzztest::VectorOf;

/**
 * The `perso_tlv_get_cert_obj` method has the following parameters:
 * - `uint8_t *buf`
 * - `size_t ltv_buf_size`
 * - `perso_tlv_cert_obj_t *obj`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void GetCertObjNeverCrashes(std::vector<uint8_t> buffer) {
  // Required Data
  perso_tlv_cert_obj_t obj{};

  // Execute Function

  [[maybe_unused]] rom_error_t error =
      perso_tlv_get_cert_obj(buffer.data(), buffer.size(), &obj);

  if (error == kErrorOk) {
    EXPECT_GE(obj.obj_type, 0);
    EXPECT_LE(obj.obj_type, 7);
  }
}

/**
 * The `perso_tlv_cert_obj_build` method has the following parameters:
 * - `uint8_t *buf`
 * - `size_t ltv_buf_size`
 * - `perso_tlv_cert_obj_t *obj`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void CertObjBuildNeverCrashes(std::string name, const uint32_t obj_type,
                              std::vector<uint8_t> cert,
                              std::vector<uint8_t> buffer) {
  // Required Data

  size_t buffer_size_var = buffer.size();

  // Execute Function

  [[maybe_unused]] rom_error_t error = perso_tlv_cert_obj_build(
      name.c_str(), (perso_tlv_object_type_t)obj_type, cert.data(), cert.size(),
      buffer.data(), &buffer_size_var);
}

FUZZ_TEST(PersoTlvDataFuzzTest, GetCertObjNeverCrashes)
    .WithDomains(fuzztest::VectorOf(fuzztest::Arbitrary<uint8_t>()));
FUZZ_TEST(PersoTlvDataFuzzTest, CertObjBuildNeverCrashes)
    .WithDomains(Arbitrary<std::string>(), Arbitrary<uint32_t>(),
                 VectorOf(Arbitrary<uint8_t>()),
                 VectorOf(Arbitrary<uint8_t>()));
}  // namespace
}  // namespace perso_tlv_data_fuzztest
