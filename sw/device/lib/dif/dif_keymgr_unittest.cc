// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_keymgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "keymgr_regs.h"  // Generated

namespace dif_keymgr_unittest {
namespace {

/**
 * Returns a `uint32_t` with a single zero bit.
 */
uint32_t AllOnesExcept(uint32_t index) { return ~(1u << index); }

/**
 * Returns a vector of values for a given enum type.
 *
 * Assumes that the values are sequential and the first value is 0. `last` must
 * be the last valid value for the given enum and is included in the returned
 * vector.
 */
template <typename T>
std::vector<T> CreateEnumVector(T last) {
  using TT = typename std::underlying_type<T>::type;
  std::vector<T> res;
  for (TT i = 0; i <= static_cast<TT>(last); ++i) {
    res.push_back(static_cast<T>(i));
  }
  return res;
}

/**
 * Returns a seemingly valid, i.e. nonzero, pointer for the given type or a
 * `nullptr`.
 */
template <typename T>
T *GetGoodBadPtrArg(bool is_good) {
  if (is_good) {
    return reinterpret_cast<T *>(alignof(T));
  } else {
    return nullptr;
  }
}

/**
 * Returns a valid or invalid value for the given enum type.
 *
 * `last` must be the last valid value of the given enum type and `last+1` must
 * be an invalid value.
 */
template <typename T>
T GetGoodBadEnumArg(bool is_good, T last) {
  if (is_good) {
    return last;
  } else {
    return static_cast<T>(last + 1);
  }
}

/**
 * Constants used in tests.
 */
static constexpr std::array<uint32_t, 3> kStatesWithOperationalNextStates{
    KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
    KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY,
};
static constexpr std::array<uint32_t, 4> kStatesWithNonOperationalNextStates{
    KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
    KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY,
    KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED,
    KEYMGR_WORKING_STATE_STATE_VALUE_INVALID,
};

class DifKeymgrTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  /**
   * Parameters for initializing a `dif_keymgr_t`.
   */
  const dif_keymgr_params_t params_ = {.base_addr = dev().region()};
};

/**
 * Class for parameterizing bad argument tests for functions with two arguments.
 */
class BadArgsTwo : public DifKeymgrTest,
                   public testing::WithParamInterface<std::tuple<bool, bool>> {
 protected:
  bool AllParamsGood() {
    return std::get<0>(GetParam()) && std::get<1>(GetParam());
  }

  void SetUp() override {
    if (AllParamsGood()) {
      // Only test negative cases.
      GTEST_SKIP();
    }
  }
};

INSTANTIATE_TEST_SUITE_P(
    BadArgsTwo, BadArgsTwo, testing::Combine(testing::Bool(), testing::Bool()),
    [&](testing::TestParamInfo<std::tuple<bool, bool>> info) {
      auto stringify = [](bool foo) { return foo ? "Good" : "Bad"; };
      std::stringstream ss;
      ss << stringify(std::get<0>(info.param))
         << stringify(std::get<1>(info.param));
      return ss.str();
    });

/**
 * Class for parameterizing bad argument tests for functions with three
 * arguments.
 */
class BadArgsThree
    : public DifKeymgrTest,
      public testing::WithParamInterface<std::tuple<bool, bool, bool>> {
 protected:
  bool AllParamsGood() {
    return std::get<0>(GetParam()) && std::get<1>(GetParam()) &&
           std::get<2>(GetParam());
  }

  void SetUp() override {
    if (AllParamsGood()) {
      // Only test negative cases.
      GTEST_SKIP();
    }
  }
};

INSTANTIATE_TEST_SUITE_P(
    BadArgsThree, BadArgsThree,
    testing::Combine(testing::Bool(), testing::Bool(), testing::Bool()),
    [&](testing::TestParamInfo<std::tuple<bool, bool, bool>> info) {
      auto stringify = [](bool foo) { return foo ? "Good" : "Bad"; };
      std::stringstream ss;
      ss << stringify(std::get<0>(info.param))
         << stringify(std::get<1>(info.param))
         << stringify(std::get<2>(info.param));
      return ss.str();
    });

class InitTest : public DifKeymgrTest {};

TEST_F(InitTest, BadArgs) {
  EXPECT_EQ(dif_keymgr_init(params_, nullptr), kDifKeymgrBadArg);
}

TEST_F(InitTest, Init) {
  dif_keymgr_t keymgr;
  EXPECT_EQ(dif_keymgr_init(params_, &keymgr), kDifKeymgrOk);
}

/**
 * Base class for the rest of the tests in this file, provides a
 * `dif_keymgr_t` instance and some methods for common expectations.
 */
class DifKeymgrInitialized : public DifKeymgrTest {
 protected:
  /**
   * Expectations for an idle key manager.
   */
  void ExpectIdle() {
    EXPECT_READ32(KEYMGR_OP_STATUS_REG_OFFSET,
                  {{
                      .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                      .value = KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                  }});
    EXPECT_READ32(KEYMGR_CFG_REGWEN_REG_OFFSET,
                  {{
                      .offset = KEYMGR_CFG_REGWEN_EN_BIT,
                      .value = 1,
                  }});
  }

  /**
   * Expectations for an idle key manager at a given state.
   */
  void ExpectIdleAtState(uint32_t state) {
    ExpectIdle();
    EXPECT_READ32(KEYMGR_WORKING_STATE_REG_OFFSET,
                  {{
                      .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                      .value = state,
                  }});
  }

  /**
   * Expectations for a busy key manager.
   */
  void ExpectBusy() {
    EXPECT_READ32(KEYMGR_OP_STATUS_REG_OFFSET,
                  {{
                      .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                      .value = KEYMGR_OP_STATUS_STATUS_VALUE_WIP,
                  }});
  }

  /**
   * Expectations for a locked CONFIG register.
   */
  void ExpectLockedConfig() {
    EXPECT_READ32(KEYMGR_OP_STATUS_REG_OFFSET,
                  {{
                      .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                      .value = KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                  }});
    EXPECT_READ32(KEYMGR_CFG_REGWEN_REG_OFFSET,
                  AllOnesExcept(KEYMGR_CFG_REGWEN_EN_BIT));
  }

  struct OperationStartParams {
    uint32_t dest_sel;
    uint32_t operation;
  };

  /**
   * Expectations for starting an operation.
   */
  void ExpectOperationStart(const OperationStartParams &params) {
    EXPECT_WRITE32(KEYMGR_CONTROL_REG_OFFSET,
                   {{
                        .offset = KEYMGR_CONTROL_DEST_SEL_OFFSET,
                        .value = params.dest_sel,
                    },
                    {
                        .offset = KEYMGR_CONTROL_OPERATION_OFFSET,
                        .value = params.operation,
                    },
                    {
                        .offset = KEYMGR_CONTROL_START_BIT,
                        .value = 1,
                    }});
  }

  /**
   * Initialized `dif_keymgr_t` used in tests.
   */
  const dif_keymgr_t keymgr_ = {.params = params_};
};

class ConfigureTest : public DifKeymgrInitialized {};

TEST_F(ConfigureTest, BadArgs) {
  EXPECT_EQ(dif_keymgr_configure(nullptr, {}), kDifKeymgrBadArg);
}

TEST_F(ConfigureTest, Configure) {
  constexpr dif_keymgr_config_t kConfig = {.entropy_reseed_interval = 0xA5A5};

  EXPECT_WRITE32(KEYMGR_RESEED_INTERVAL_REG_OFFSET,
                 kConfig.entropy_reseed_interval);

  EXPECT_EQ(dif_keymgr_configure(&keymgr_, kConfig), kDifKeymgrOk);
}

class AdvanceStateTest : public DifKeymgrInitialized {
 protected:
  dif_keymgr_state_params_t kStateParams{
      .binding_value = {0xFF, 0xC3, 0xB9, 0xA5, 0x00, 0x3C, 0x46, 0x5A},
      .max_key_version = 0xA5A5A5A5,
  };

  struct MaxKeyVersionRegInfo {
    uint32_t offset;
    uint32_t wen_offset;
    uint32_t wen_bit_index;
  };

  /**
   * Returns max key version register information for the given state.
   */
  MaxKeyVersionRegInfo GetMaxKeyVersionRegInfo(uint32_t state) {
    switch (state) {
      case KEYMGR_WORKING_STATE_STATE_VALUE_INIT:
        return {
            .offset = KEYMGR_MAX_CREATOR_KEY_VER_REG_OFFSET,
            .wen_offset = KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET,
            .wen_bit_index = KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_EN_BIT,
        };
      case KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY:
        return {
            .offset = KEYMGR_MAX_OWNER_INT_KEY_VER_REG_OFFSET,
            .wen_offset = KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_OFFSET,
            .wen_bit_index = KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_EN_BIT,
        };
      case KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY:
        return {
            .offset = KEYMGR_MAX_OWNER_KEY_VER_REG_OFFSET,
            .wen_offset = KEYMGR_MAX_OWNER_KEY_VER_REGWEN_REG_OFFSET,
            .wen_bit_index = KEYMGR_MAX_OWNER_KEY_VER_REGWEN_EN_BIT,
        };
      default:
        ADD_FAILURE();
        abort();
        break;
    }
  }
};

TEST_F(AdvanceStateTest, BadArgsNoKeymgr) {
  EXPECT_EQ(dif_keymgr_advance_state(nullptr, &kStateParams),
            kDifKeymgrLockableBadArg);
  EXPECT_EQ(dif_keymgr_advance_state(nullptr, nullptr),
            kDifKeymgrLockableBadArg);
}

class AdvanceToOperational : public AdvanceStateTest,
                             public testing::WithParamInterface<uint32_t> {};

TEST_P(AdvanceToOperational, BadArgsToOperationalWithoutParams) {
  ExpectIdleAtState(GetParam());

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, nullptr),
            kDifKeymgrLockableBadArg);
}

INSTANTIATE_TEST_SUITE_P(AdvanceToOperational, AdvanceToOperational,
                         testing::ValuesIn(kStatesWithOperationalNextStates));

class AdvanceToNonOperational : public AdvanceStateTest,
                                public testing::WithParamInterface<uint32_t> {};

TEST_P(AdvanceToNonOperational, BadArgsToNonOperationalWithParams) {
  ExpectIdleAtState(GetParam());

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableBadArg);
}

INSTANTIATE_TEST_SUITE_P(
    AdvanceToNonOperational, AdvanceToNonOperational,
    testing::ValuesIn(kStatesWithNonOperationalNextStates));

TEST_F(AdvanceStateTest, LockedBusy) {
  ExpectBusy();

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableLocked);
}

TEST_F(AdvanceStateTest, LockedConfig) {
  ExpectLockedConfig();

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableLocked);
}

TEST_P(AdvanceToOperational, LockedBinding) {
  ExpectIdleAtState(GetParam());
  EXPECT_READ32(KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableLocked);
}

TEST_P(AdvanceToOperational, LockedMaxKeyVersion) {
  ExpectIdleAtState(GetParam());
  EXPECT_READ32(KEYMGR_SW_BINDING_REGWEN_REG_OFFSET,
                {{
                    .offset = KEYMGR_SW_BINDING_REGWEN_EN_BIT,
                    .value = 1,
                }});
  EXPECT_READ32(GetMaxKeyVersionRegInfo(GetParam()).wen_offset, 0);

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableLocked);
}

TEST_P(AdvanceToOperational, Success) {
  ExpectIdleAtState(GetParam());
  EXPECT_READ32(KEYMGR_SW_BINDING_REGWEN_REG_OFFSET,
                {{
                    .offset = KEYMGR_SW_BINDING_REGWEN_EN_BIT,
                    .value = 1,
                }});
  auto reg_info = GetMaxKeyVersionRegInfo(GetParam());
  EXPECT_READ32(reg_info.wen_offset, {{
                                         .offset = reg_info.wen_bit_index,
                                         .value = 1,
                                     }});
  size_t binding_len = sizeof(kStateParams.binding_value) /
                       sizeof(kStateParams.binding_value[0]);
  for (size_t i = 0; i < binding_len; ++i) {
    EXPECT_WRITE32(KEYMGR_SW_BINDING_0_REG_OFFSET + i * 4,
                   kStateParams.binding_value[i]);
  }
  EXPECT_WRITE32(KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);
  EXPECT_WRITE32(reg_info.offset, kStateParams.max_key_version);
  EXPECT_WRITE32(reg_info.wen_offset, 0);
  ExpectOperationStart({
      .dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
      .operation = KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE,
  });

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, &kStateParams),
            kDifKeymgrLockableOk);
}

TEST_P(AdvanceToNonOperational, Success) {
  ExpectIdleAtState(GetParam());
  ExpectOperationStart({
      .dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
      .operation = KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE,
  });

  EXPECT_EQ(dif_keymgr_advance_state(&keymgr_, nullptr), kDifKeymgrLockableOk);
}

class DisableTest : public DifKeymgrInitialized {};

TEST_F(DisableTest, BadArgs) {
  EXPECT_EQ(dif_keymgr_disable(nullptr), kDifKeymgrLockableBadArg);
}

TEST_F(DisableTest, LockedBusy) {
  ExpectBusy();
  EXPECT_EQ(dif_keymgr_disable(&keymgr_), kDifKeymgrLockableLocked);
}

TEST_F(DisableTest, LockedConfig) {
  ExpectLockedConfig();

  EXPECT_EQ(dif_keymgr_disable(&keymgr_), kDifKeymgrLockableLocked);
}

TEST_F(DisableTest, Disable) {
  ExpectIdle();
  ExpectOperationStart({
      .dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
      .operation = KEYMGR_CONTROL_OPERATION_VALUE_DISABLE,
  });

  EXPECT_EQ(dif_keymgr_disable(&keymgr_), kDifKeymgrLockableOk);
}

TEST_P(BadArgsTwo, GetStatusCodes) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto status_codes =
      GetGoodBadPtrArg<dif_keymgr_status_codes_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_get_status_codes(keymgr, status_codes),
            kDifKeymgrBadArg);
}

struct GetStatusCodesTestCase {
  /**
   * Values of OP_STATUS or ERR_CODE registers.
   */
  std::vector<mock_mmio::BitField> reg_val;
  /**
   * Expected output of `dif_keymgr_get_status_codes()`.
   */
  dif_keymgr_status_codes_t exp_val;
};

class GetStatusCodesNoError
    : public DifKeymgrInitialized,
      public testing::WithParamInterface<GetStatusCodesTestCase> {};

TEST_P(GetStatusCodesNoError, Success) {
  EXPECT_READ32(KEYMGR_OP_STATUS_REG_OFFSET, GetParam().reg_val);
  EXPECT_WRITE32(KEYMGR_OP_STATUS_REG_OFFSET, GetParam().reg_val);

  dif_keymgr_status_codes_t act_val;
  EXPECT_EQ(dif_keymgr_get_status_codes(&keymgr_, &act_val), kDifKeymgrOk);
  EXPECT_EQ(GetParam().exp_val, act_val);
}

INSTANTIATE_TEST_SUITE_P(
    GetStatusCodesNoError, GetStatusCodesNoError,
    testing::Values(
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                .value = KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                .value = KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_OP_STATUS_STATUS_OFFSET,
                .value = KEYMGR_OP_STATUS_STATUS_VALUE_WIP,
            }},
            .exp_val = 0,
        }));

class GetStatusCodesWithError
    : public DifKeymgrInitialized,
      public testing::WithParamInterface<GetStatusCodesTestCase> {};

TEST_P(GetStatusCodesWithError, Success) {
  EXPECT_READ32(KEYMGR_OP_STATUS_REG_OFFSET,
                KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_WRITE32(KEYMGR_OP_STATUS_REG_OFFSET,
                 KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_READ32(KEYMGR_ERR_CODE_REG_OFFSET, GetParam().reg_val);
  EXPECT_WRITE32(KEYMGR_ERR_CODE_REG_OFFSET, GetParam().reg_val);

  dif_keymgr_status_codes_t act_val;
  EXPECT_EQ(dif_keymgr_get_status_codes(&keymgr_, &act_val), kDifKeymgrOk);
  EXPECT_EQ(GetParam().exp_val, act_val);
}

INSTANTIATE_TEST_SUITE_P(
    GetStatusCodesWithError, GetStatusCodesWithError,
    testing::Values(
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_ERR_CODE_INVALID_OP_BIT,
                .value = 1,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidOperation,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_ERR_CODE_INVALID_CMD_BIT,
                .value = 1,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidKmacCommand,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_ERR_CODE_INVALID_KMAC_INPUT_BIT,
                .value = 1,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidKmacInput,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                .offset = KEYMGR_ERR_CODE_INVALID_KMAC_DATA_BIT,
                .value = 1,
            }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidKmacOutput,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                            .offset = KEYMGR_ERR_CODE_INVALID_OP_BIT,
                            .value = 1,
                        },
                        {
                            .offset = KEYMGR_ERR_CODE_INVALID_KMAC_INPUT_BIT,
                            .value = 1,
                        }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidOperation |
                       kDifKeymgrStatusCodeInvalidKmacInput,
        },
        GetStatusCodesTestCase{
            .reg_val = {{
                            .offset = KEYMGR_ERR_CODE_INVALID_CMD_BIT,
                            .value = 1,
                        },
                        {
                            .offset = KEYMGR_ERR_CODE_INVALID_KMAC_DATA_BIT,
                            .value = 1,
                        }},
            .exp_val = kDifKeymgrStatusCodeIdle |
                       kDifKeymgrStatusCodeInvalidKmacCommand |
                       kDifKeymgrStatusCodeInvalidKmacOutput,
        }));

class GetStateTest : public DifKeymgrInitialized {};

TEST_P(BadArgsTwo, GetState) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto state = GetGoodBadPtrArg<dif_keymgr_state_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_get_state(keymgr, state), kDifKeymgrBadArg);
}

struct GetStateTestCase {
  /**
   * Value of the WORKING_STATE register.
   */
  std::vector<mock_mmio::BitField> reg_val;
  /**
   * Expected output of `dif_keymgr_get_state()`.
   */
  dif_keymgr_state_t exp_output;
};

class GetState : public GetStateTest,
                 public testing::WithParamInterface<GetStateTestCase> {};

TEST_P(GetState, Success) {
  EXPECT_READ32(KEYMGR_WORKING_STATE_REG_OFFSET, GetParam().reg_val);

  dif_keymgr_state_t state;
  EXPECT_EQ(dif_keymgr_get_state(&keymgr_, &state), kDifKeymgrOk);
  EXPECT_EQ(state, GetParam().exp_output);
}

INSTANTIATE_TEST_SUITE_P(
    AllValidStates, GetState,
    testing::Values(
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
            }},
            .exp_output = kDifKeymgrStateReset,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
            }},
            .exp_output = kDifKeymgrStateInitialized,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
            }},
            .exp_output = kDifKeymgrStateCreatorRootKey,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value =
                    KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY,
            }},
            .exp_output = kDifKeymgrStateOwnerIntermediateKey,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY,
            }},
            .exp_output = kDifKeymgrStateOwnerRootKey,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED,
            }},
            .exp_output = kDifKeymgrStateDisabled,
        },
        GetStateTestCase{
            .reg_val = {{
                .offset = KEYMGR_WORKING_STATE_STATE_OFFSET,
                .value = KEYMGR_WORKING_STATE_STATE_VALUE_INVALID,
            }},
            .exp_output = kDifKeymgrStateInvalid,
        }));

TEST_F(GetStateTest, UnexpectedState) {
  EXPECT_READ32(KEYMGR_WORKING_STATE_REG_OFFSET,
                KEYMGR_WORKING_STATE_STATE_MASK);

  dif_keymgr_state_t state;
  EXPECT_EQ(dif_keymgr_get_state(&keymgr_, &state), kDifKeymgrError);
}

class GenerateIdentityTest : public DifKeymgrInitialized {};

TEST_F(GenerateIdentityTest, BadArgs) {
  EXPECT_EQ(dif_keymgr_generate_identity_seed(nullptr),
            kDifKeymgrLockableBadArg);
}

TEST_F(GenerateIdentityTest, LockedBusy) {
  ExpectBusy();

  EXPECT_EQ(dif_keymgr_generate_identity_seed(&keymgr_),
            kDifKeymgrLockableLocked);
}

TEST_F(GenerateIdentityTest, LockedConfig) {
  ExpectLockedConfig();

  EXPECT_EQ(dif_keymgr_generate_identity_seed(&keymgr_),
            kDifKeymgrLockableLocked);
}

TEST_F(GenerateIdentityTest, Generate) {
  ExpectIdle();
  ExpectOperationStart({
      .dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
      .operation = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_ID,
  });

  EXPECT_EQ(dif_keymgr_generate_identity_seed(&keymgr_), kDifKeymgrLockableOk);
}

class GenerateVersionedKeyTest : public DifKeymgrInitialized {};

TEST_P(BadArgsTwo, GenerateVersionedKey) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto dest = GetGoodBadEnumArg<dif_keymgr_versioned_key_dest_t>(
      std::get<1>(GetParam()), kDifKeymgrVersionedKeyDestLast);

  EXPECT_EQ(dif_keymgr_generate_versioned_key(keymgr, {.dest = dest}),
            kDifKeymgrLockableBadArg);
}

TEST_F(GenerateVersionedKeyTest, LockedBusy) {
  ExpectBusy();

  EXPECT_EQ(dif_keymgr_generate_versioned_key(&keymgr_, {}),
            kDifKeymgrLockableLocked);
}

TEST_F(GenerateVersionedKeyTest, LockedConfig) {
  ExpectLockedConfig();

  EXPECT_EQ(dif_keymgr_generate_versioned_key(&keymgr_, {}),
            kDifKeymgrLockableLocked);
}

struct GenerateVersionedKeyTestCase {
  /**
   * Destination of the generated key.
   */
  dif_keymgr_versioned_key_dest_t dest;
  /**
   * Expected DEST_SEL value to be written to the CONTROL register.
   */
  uint32_t exp_dest_sel;
  /**
   * Expected OPERATION values to be written to the CONTROL register.
   */
  uint32_t exp_operation;
};

class GenerateVersionedKey
    : public GenerateVersionedKeyTest,
      public testing::WithParamInterface<GenerateVersionedKeyTestCase> {};

TEST_P(GenerateVersionedKey, Success) {
  dif_keymgr_versioned_key_params_t params{
      .dest = GetParam().dest,
      .salt = {0x5A, 0x46, 0x3C, 0x00, 0xA5, 0xB9, 0xC3, 0xFF},
      .version = 0xA5A5A5A5,
  };

  ExpectIdle();
  size_t salt_len = sizeof(params.salt) / sizeof(params.salt[0]);
  for (size_t i = 0; i < salt_len; ++i) {
    EXPECT_WRITE32(KEYMGR_SALT_0_REG_OFFSET + i * 4, params.salt[i]);
  }
  EXPECT_WRITE32(KEYMGR_KEY_VERSION_REG_OFFSET, params.version);
  ExpectOperationStart({
      .dest_sel = GetParam().exp_dest_sel,
      .operation = GetParam().exp_operation,
  });

  EXPECT_EQ(dif_keymgr_generate_versioned_key(&keymgr_, params),
            kDifKeymgrLockableOk);
}

INSTANTIATE_TEST_SUITE_P(
    GenerateVersionedKeyAllDests, GenerateVersionedKey,
    testing::Values(
        GenerateVersionedKeyTestCase{
            .dest = kDifKeymgrVersionedKeyDestSw,
            .exp_dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
            .exp_operation = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_SW_OUTPUT,
        },
        GenerateVersionedKeyTestCase{
            .dest = kDifKeymgrVersionedKeyDestAes,
            .exp_dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_AES,
            .exp_operation = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
        },
        GenerateVersionedKeyTestCase{
            .dest = kDifKeymgrVersionedKeyDestHmac,
            .exp_dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_HMAC,
            .exp_operation = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
        },
        GenerateVersionedKeyTestCase{
            .dest = kDifKeymgrVersionedKeyDestKmac,
            .exp_dest_sel = KEYMGR_CONTROL_DEST_SEL_VALUE_KMAC,
            .exp_operation = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
        }));

class SideloadClearTest : public DifKeymgrInitialized {};

TEST_P(BadArgsTwo, GetBadArg) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto state = GetGoodBadPtrArg<dif_keymgr_toggle_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_sideload_clear_get_enabled(keymgr, state),
            kDifKeymgrBadArg);
}

TEST_P(BadArgsTwo, SetBadArg) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto state = GetGoodBadEnumArg<dif_keymgr_toggle_t>(std::get<1>(GetParam()),
                                                      kDifKeymgrToggleDisabled);

  EXPECT_EQ(dif_keymgr_sideload_clear_set_enabled(keymgr, state),
            kDifKeymgrBadArg);
}

TEST_F(SideloadClearTest, Set) {
  EXPECT_WRITE32(KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                 {{
                     .offset = KEYMGR_SIDELOAD_CLEAR_VAL_BIT,
                     .value = 1,
                 }});
  EXPECT_EQ(
      dif_keymgr_sideload_clear_set_enabled(&keymgr_, kDifKeymgrToggleEnabled),
      kDifKeymgrOk);

  EXPECT_WRITE32(KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                 {{
                     .offset = KEYMGR_SIDELOAD_CLEAR_VAL_BIT,
                     .value = 0,
                 }});
  EXPECT_EQ(
      dif_keymgr_sideload_clear_set_enabled(&keymgr_, kDifKeymgrToggleDisabled),
      kDifKeymgrOk);
}

TEST_F(SideloadClearTest, Get) {
  EXPECT_READ32(KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                {{
                    .offset = KEYMGR_SIDELOAD_CLEAR_VAL_BIT,
                    .value = 1,
                }});
  dif_keymgr_toggle_t state = kDifKeymgrToggleDisabled;
  EXPECT_EQ(dif_keymgr_sideload_clear_get_enabled(&keymgr_, &state),
            kDifKeymgrOk);
  EXPECT_EQ(state, kDifKeymgrToggleEnabled);

  EXPECT_READ32(KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                {{
                    .offset = KEYMGR_SIDELOAD_CLEAR_VAL_BIT,
                    .value = 0,
                }});
  state = kDifKeymgrToggleEnabled;
  EXPECT_EQ(dif_keymgr_sideload_clear_get_enabled(&keymgr_, &state),
            kDifKeymgrOk);
  EXPECT_EQ(state, kDifKeymgrToggleDisabled);
}

class ReadOutputTest : public DifKeymgrInitialized {};

TEST_P(BadArgsTwo, ReadOutput) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto output = GetGoodBadPtrArg<dif_keymgr_output_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_read_output(keymgr, output), kDifKeymgrBadArg);
}

TEST_F(ReadOutputTest, Read) {
  constexpr size_t kNumShares = 2;
  constexpr size_t kNumShareWords = 8;
  constexpr std::array<std::array<uint32_t, kNumShareWords>, kNumShares>
      kExpected{{{0x8D, 0x25, 0x44, 0x0A, 0xEC, 0x1C, 0xAC, 0x0E},
                 {0x44, 0x5B, 0x90, 0x39, 0x24, 0x72, 0xA7, 0xCB}}};
  constexpr std::array<uint32_t, kNumShares> kShareRegOffsets{
      {KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET,
       KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET}};

  for (size_t i = 0; i < kNumShares; ++i) {
    for (size_t j = 0; j < kNumShareWords; ++j) {
      EXPECT_READ32(kShareRegOffsets[i] + j * 4, kExpected[i][j]);
    }
  }

  dif_keymgr_output_t output;
  EXPECT_EQ(dif_keymgr_read_output(&keymgr_, &output), kDifKeymgrOk);
  for (size_t i = 0; i < kNumShares; ++i) {
    EXPECT_THAT(kExpected[i], ::testing::ElementsAreArray(output.value[i]));
  }
}

TEST_P(BadArgsTwo, AlertForce) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto alert = GetGoodBadEnumArg<dif_keymgr_alert_t>(std::get<1>(GetParam()),
                                                     kDifKeymgrAlertLast);

  EXPECT_EQ(dif_keymgr_alert_force(keymgr, alert), kDifKeymgrBadArg);
}

struct AlertTestCase {
  dif_keymgr_alert_t alert;
  bitfield_bit32_index_t bit_index;
};

class AlertForce : public DifKeymgrInitialized,
                   public testing::WithParamInterface<AlertTestCase> {};

TEST_P(AlertForce, Success) {
  EXPECT_WRITE32(KEYMGR_ALERT_TEST_REG_OFFSET,
                 {{
                     .offset = GetParam().bit_index,
                     .value = 1,
                 }});

  EXPECT_EQ(dif_keymgr_alert_force(&keymgr_, GetParam().alert), kDifKeymgrOk);
}

INSTANTIATE_TEST_SUITE_P(
    AlertForceAll, AlertForce,
    testing::Values(
        AlertTestCase{
            .alert = kDifKeymgrAlertHardware,
            .bit_index = KEYMGR_ALERT_TEST_FATAL_FAULT_ERR_BIT,
        },
        AlertTestCase{
            .alert = kDifKeymgrAlertSoftware,
            .bit_index = KEYMGR_ALERT_TEST_RECOV_OPERATION_ERR_BIT,
        }));

class IrqTest : public DifKeymgrInitialized {};

TEST_P(BadArgsThree, IrqIsPending) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto irq = GetGoodBadEnumArg<dif_keymgr_irq_t>(std::get<1>(GetParam()),
                                                 kDifKeymgrIrqLast);
  auto is_pending = GetGoodBadPtrArg<bool>(std::get<2>(GetParam()));

  EXPECT_EQ(dif_keymgr_irq_is_pending(keymgr, irq, is_pending),
            kDifKeymgrBadArg);
}

class IrqIsPending
    : public IrqTest,
      public testing::WithParamInterface<std::tuple<dif_keymgr_irq_t, bool>> {};

TEST_P(IrqIsPending, IsPending) {
  auto irq = std::get<0>(GetParam());
  bool exp_val = std::get<1>(GetParam());

  EXPECT_READ32(KEYMGR_INTR_STATE_REG_OFFSET, {{
                                                  .offset = irq,
                                                  .value = exp_val,
                                              }});
  bool is_pending = !exp_val;
  EXPECT_EQ(dif_keymgr_irq_is_pending(&keymgr_, irq, &is_pending),
            kDifKeymgrOk);
  EXPECT_EQ(is_pending, exp_val);
}

INSTANTIATE_TEST_SUITE_P(
    IsPendingAllIrqs, IrqIsPending,
    testing::Combine(testing::ValuesIn(
                         CreateEnumVector<dif_keymgr_irq_t>(kDifKeymgrIrqLast)),
                     testing::Bool()));

TEST_P(BadArgsTwo, IrqAck) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto irq = GetGoodBadEnumArg<dif_keymgr_irq_t>(std::get<1>(GetParam()),
                                                 kDifKeymgrIrqLast);

  EXPECT_EQ(dif_keymgr_irq_acknowledge(keymgr, irq), kDifKeymgrBadArg);
}

class Irq : public IrqTest,
            public testing::WithParamInterface<dif_keymgr_irq_t> {};

TEST_P(Irq, Ack) {
  EXPECT_WRITE32(KEYMGR_INTR_STATE_REG_OFFSET, {{
                                                   .offset = GetParam(),
                                                   .value = 1,
                                               }});

  EXPECT_EQ(dif_keymgr_irq_acknowledge(&keymgr_, GetParam()), kDifKeymgrOk);
}

INSTANTIATE_TEST_SUITE_P(
    AllIrqs, Irq,
    testing::ValuesIn(CreateEnumVector<dif_keymgr_irq_t>(kDifKeymgrIrqLast)));

TEST_P(BadArgsThree, GetEnabled) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto irq = GetGoodBadEnumArg<dif_keymgr_irq_t>(std::get<1>(GetParam()),
                                                 kDifKeymgrIrqLast);
  auto is_enabled =
      GetGoodBadPtrArg<dif_keymgr_toggle_t>(std::get<2>(GetParam()));

  EXPECT_EQ(dif_keymgr_irq_get_enabled(keymgr, irq, is_enabled),
            kDifKeymgrBadArg);
}

class IrqGetSetEnabled
    : public IrqTest,
      public testing::WithParamInterface<
          std::tuple<dif_keymgr_irq_t, dif_keymgr_toggle_t>> {};

TEST_P(IrqGetSetEnabled, GetEnabled) {
  auto irq = std::get<0>(GetParam());
  auto exp_val = std::get<1>(GetParam());

  EXPECT_READ32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                {{
                    .offset = irq,
                    .value = (exp_val == kDifKeymgrToggleEnabled),
                }});

  dif_keymgr_toggle_t is_enabled = (exp_val == kDifKeymgrToggleEnabled)
                                       ? kDifKeymgrToggleDisabled
                                       : kDifKeymgrToggleEnabled;
  EXPECT_EQ(dif_keymgr_irq_get_enabled(&keymgr_, irq, &is_enabled),
            kDifKeymgrOk);
  EXPECT_EQ(is_enabled, exp_val);
}

INSTANTIATE_TEST_SUITE_P(
    AllIrqsAndToggles, IrqGetSetEnabled,
    testing::Combine(testing::ValuesIn(
                         CreateEnumVector<dif_keymgr_irq_t>(kDifKeymgrIrqLast)),
                     testing::ValuesIn(CreateEnumVector<dif_keymgr_toggle_t>(
                         kDifKeymgrToggleDisabled))));

TEST_P(BadArgsThree, SetEnabled) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto irq = GetGoodBadEnumArg<dif_keymgr_irq_t>(std::get<1>(GetParam()),
                                                 kDifKeymgrIrqLast);
  auto state = GetGoodBadEnumArg<dif_keymgr_toggle_t>(std::get<2>(GetParam()),
                                                      kDifKeymgrToggleDisabled);

  EXPECT_EQ(dif_keymgr_irq_set_enabled(keymgr, irq, state), kDifKeymgrBadArg);
}

TEST_P(IrqGetSetEnabled, SetEnabled) {
  auto irq = std::get<0>(GetParam());
  auto new_state = std::get<1>(GetParam());
  EXPECT_MASK32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                {{
                    .offset = irq,
                    .mask = 1,
                    .value = (new_state == kDifKeymgrToggleEnabled),
                }});

  EXPECT_EQ(dif_keymgr_irq_set_enabled(&keymgr_, irq, new_state), kDifKeymgrOk);
}

TEST_P(BadArgsTwo, IrqForce) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto irq = GetGoodBadEnumArg<dif_keymgr_irq_t>(std::get<1>(GetParam()),
                                                 kDifKeymgrIrqLast);

  EXPECT_EQ(dif_keymgr_irq_force(keymgr, irq), kDifKeymgrBadArg);
}

TEST_P(Irq, Force) {
  EXPECT_WRITE32(KEYMGR_INTR_TEST_REG_OFFSET, {{
                                                  .offset = GetParam(),
                                                  .value = 1,
                                              }});

  EXPECT_EQ(dif_keymgr_irq_force(&keymgr_, GetParam()), kDifKeymgrOk);
}

TEST_P(BadArgsTwo, DisableAll) {
  // `snapshot` (second argument) is optional, skip if `keymgr` (first argument)
  // is good.
  if (std::get<0>(GetParam())) {
    GTEST_SKIP();
  }

  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto snapshot =
      GetGoodBadPtrArg<dif_keymgr_irq_snapshot_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_irq_disable_all(keymgr, snapshot), kDifKeymgrBadArg);
}

TEST_F(IrqTest, DisableAll) {
  constexpr uint32_t kExpVal = 0xA5A5A5A5;

  // With `snapshot`.
  EXPECT_READ32(KEYMGR_INTR_ENABLE_REG_OFFSET, kExpVal);
  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);

  dif_keymgr_irq_snapshot_t snapshot = 0;
  EXPECT_EQ(dif_keymgr_irq_disable_all(&keymgr_, &snapshot), kDifKeymgrOk);
  EXPECT_EQ(snapshot, kExpVal);

  // Without `snapshot`.
  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_disable_all(&keymgr_, nullptr), kDifKeymgrOk);
}

TEST_P(BadArgsTwo, IrqRestore) {
  auto keymgr = GetGoodBadPtrArg<dif_keymgr_t>(std::get<0>(GetParam()));
  auto snapshot =
      GetGoodBadPtrArg<dif_keymgr_irq_snapshot_t>(std::get<1>(GetParam()));

  EXPECT_EQ(dif_keymgr_irq_restore_all(keymgr, snapshot), kDifKeymgrBadArg);
}

TEST_F(IrqTest, RestoreAll) {
  dif_keymgr_irq_snapshot_t snapshot = 0xA5A5A5A5;

  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, snapshot);

  EXPECT_EQ(dif_keymgr_irq_restore_all(&keymgr_, &snapshot), kDifKeymgrOk);
}

}  // namespace
}  // namespace dif_keymgr_unittest
