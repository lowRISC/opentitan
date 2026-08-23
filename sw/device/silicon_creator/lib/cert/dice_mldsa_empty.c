#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice_mldsa.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/mldsa_key.h"

OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_mldsa_tbs_cert_generate_and_build(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement,
    const hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    const hmac_digest_t *otp_rot_creator_auth_state_measurement,
    const cert_key_id_pair_t *key_ids, mldsa_parameter_set_t mldsa_params_set,
    uint8_t *tbs_cert_buffer, size_t *tbs_cert_size) {
  OT_DISCARD(otp_creator_sw_cfg_measurement);
  OT_DISCARD(otp_owner_sw_cfg_measurement);
  OT_DISCARD(otp_rot_creator_auth_codesign_measurement);
  OT_DISCARD(otp_rot_creator_auth_state_measurement);
  OT_DISCARD(key_ids);
  OT_DISCARD(mldsa_params_set);
  OT_DISCARD(tbs_cert_buffer);
  OT_DISCARD(tbs_cert_size);
  return kErrorDiceMldsaNotImplemented;
}
