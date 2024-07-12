// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom.h"

#include <stdbool.h>
#include <stdint.h>

#include <assert.h>
#include <stdalign.h>
#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/cfi.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom/boot_policy.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"
#include "sw/device/silicon_creator/rom/rom_epmp.h"
#include "sw/device/silicon_creator/rom/sigverify_keys.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/silicon_creator/lib/rom_print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/silicon_creator/rom/alsaqr-padframe/bitfield.h"
#include "sw/device/silicon_creator/rom/alsaqr-padframe/alsaqr_periph_padframe_periphs_regs.h"
#include "sw/device/silicon_creator/rom/alsaqr-padframe/alsaqr_periph_padframe.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

/**
 * Table of forward branch Control Flow Integrity (CFI) counters.
 *
 * Columns: Name, Initital Value.
 *
 * Each counter is indexed by Name. The Initial Value is used to initialize the
 * counters with unique values with a good hamming distance. The values are
 * restricted to 11-bit to be able use immediate load instructions.

 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 6 -n 11 \
 *     -s 1630646358 --language=c
 *
 * Minimum Hamming distance: 6
 * Maximum Hamming distance: 8
 * Minimum Hamming weight: 5
 * Maximum Hamming weight: 8
 */
// clang-format off
#define ROM_CFI_FUNC_COUNTERS_TABLE(X) \
  X(kCfiRomMain,         0x14b) \
  X(kCfiRomInit,         0x7dc) \
  X(kCfiRomVerify,       0x5a7) \
  X(kCfiRomTryBoot,      0x235) \
  X(kCfiRomPreBootCheck, 0x43a) \
  X(kCfiRomBoot,         0x2e2)
// clang-format

#define TARGET_SYNTHESIS

// Define counters and constant values required by the CFI counter macros.
CFI_DEFINE_COUNTERS(rom_counters, ROM_CFI_FUNC_COUNTERS_TABLE);

// Life cycle state of the chip.
lifecycle_state_t lc_state = (lifecycle_state_t)0;
// Spi Host handler
static dif_spi_host_t spi_host;

boot_data_t boot_data = {0};
OT_ALWAYS_INLINE
static rom_error_t rom_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorInterrupt + mcause;
}

/**
 * Prints a status message indicating that the ROM is entering bootstrap mode.
 */
/*
static void rom_bootstrap_message(void) {
  rom_printf("Bootin some fresh cochina!\r\n");
  printf("Bootin some fresh cochina!\r\n");
}
*/
void init_spi_host(dif_spi_host_t *spi_host,
                   uint32_t peripheral_clock_freq_hz) {
  dif_spi_host_config_t config = {
      .spi_clock = peripheral_clock_freq_hz / 8,// consider 50MHz default ot freq, 6.25MHz after /8
      .peripheral_clock_freq_hz = peripheral_clock_freq_hz,
      .chip_select = {.idle = 2, .trail = 2, .lead = 2},
      .full_cycle = true,
      .cpha = true,
      .cpol = true,
  };
  CHECK_DIF_OK(dif_spi_host_configure(spi_host, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/true));
}
void spi_flash_load_data(void){

  volatile int * datapath;
  volatile int * address, * start, * payload_1, * payload_2, * payload_3, * test; 

  int num_iter = 195;
  int buf_size = 63;
  uint32_t buf[buf_size];
  dif_spi_host_segment_t segments[3];
  uint32_t addr = 0;
  uint32_t addr_swap = 0;
  int index = 0;
  uintptr_t base_addr = TOP_EARLGREY_SPI_HOST0_BASE_ADDR;
  uint64_t clkHz = 50000000;
  
  payload_1  = (int *) 0xff000000;
  payload_2  = (int *) 0xff000004;
  payload_3  = (int *) 0xff000008;
  address    = (int *) 0xff00000C;
  start      = (int *) 0xff000010;
  datapath   = (int *) 0xff00001C;

  alsaqr_periph_padframe_periphs_ot_spi_00_mux_set( 1 );
  alsaqr_periph_padframe_periphs_ot_spi_01_mux_set( 1 );
  alsaqr_periph_padframe_periphs_ot_spi_02_mux_set( 1 );
  alsaqr_periph_padframe_periphs_ot_spi_03_mux_set( 1 );

  CHECK_DIF_OK(dif_spi_host_init(mmio_region_from_addr(base_addr), &spi_host));
  init_spi_host(&spi_host, (uint32_t)clkHz);

  *datapath = 1;
  *address = 0;
  // load data from SPI flash
  for(int j=0;j<num_iter;j++){
     addr = j*sizeof(buf);
     addr_swap = bitfield_byteswap32(addr);
     segments[0] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeOpcode,
                   .opcode = 0x13,
     };
     segments[1] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeAddress,
                   .address =
                      {
                          .width = kDifSpiHostWidthStandard,
                          .mode = kDifSpiHostAddrMode4b,
                          .address = addr_swap,
                      },
     }; 
     segments[2] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeRx,
                   .rx =
                      {
                          .width = kDifSpiHostWidthStandard,
                          .buf = buf,
                          .length= sizeof(buf),
                      },
     };

     CHECK_DIF_OK(
          dif_spi_host_transaction(&spi_host, 0, segments, ARRAYSIZE(segments)));
     // write data to embdedded emulated flash
     for(int i = 0; i < buf_size; i += 3) {
       if(i + 2 < buf_size) {
         *payload_1 = buf[i];
         *payload_2 = buf[i+1];
         *payload_3 = buf[i+2];
	       *address   = index;
         *start = 0x1;
	 index++;
       }
     }
  }

  *datapath = 0;
  test = (int *) 0xf0000000;

  if(*test == 0x01010101)
    *test= 0x0;
  
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spi_host, false));
}
  
/**
 * Performs once-per-boot initialization of ROM modules and peripherals.
 */
static rom_error_t rom_init(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomInit, 1);
  sec_mmio_init();
  // Initialize pinmux configuration so we can use the UART.
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);
  #ifdef TARGET_SYNTHESIS                
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  // There are no conditional checks before writing to this CSR because it is
  // expected that if relevant Ibex countermeasures are disabled, this will
  // result in a nop.
  CSR_WRITE(CSR_REG_SECURESEED, rnd_uint32());

  // Write the OTP value to bits 0 to 5 of the cpuctrl CSR.
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x3f, .index = 0},
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET));
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);

  lc_state = lifecycle_state_get();

  // Update epmp config for debug rom according to lifecycle state.
  rom_epmp_config_debug_rom(lc_state);

  // Re-initialize the watchdog timer.
  watchdog_init(lc_state);
  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);

  // Initialize the shutdown policy.
  HARDENED_RETURN_IF_ERROR(shutdown_init(lc_state));

  flash_ctrl_init();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit);

  // Initialize in-memory copy of the ePMP register configuration.
  rom_epmp_state_init(lc_state);

  // Check that AST is in the expected state.
  HARDENED_RETURN_IF_ERROR(ast_check(lc_state));

  // Initialize the retention RAM based on the reset reason and the OTP value.
  // Note: Retention RAM is always reset on PoR regardless of the OTP value.
  uint32_t reset_reasons = rstmgr_reason_get();
  uint32_t reset_mask =
      (1 << kRstmgrReasonPowerOn) |
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RET_RAM_RESET_MASK_OFFSET);
  if ((reset_reasons & reset_mask) != 0) {
    retention_sram_init();
  }
  // Store the reset reason in retention RAM and clear the register.
  retention_sram_get()->reset_reasons = reset_reasons;
  rstmgr_reason_clear(reset_reasons);

  // This function is a NOP unless ROM is built for an fpga.
  device_fpga_version_print();

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/1);

  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomInit, 2);
  return kErrorOk;
}

/**
 * Verifies a ROM_EXT.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * its `identifier` and `security_version` fields, and verifies its signature.
 *
 * @param Manifest of the ROM_EXT to be verified.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
static rom_error_t rom_verify(const manifest_t *manifest,
                              uint32_t *flash_exec) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 1);
  *flash_exec = 0;
  HARDENED_RETURN_IF_ERROR(boot_policy_manifest_check(manifest, &boot_data));

  const sigverify_rsa_key_t *key;
  HARDENED_RETURN_IF_ERROR(sigverify_rsa_key_get(
      sigverify_rsa_key_id_get(&manifest->modulus), lc_state, &key));
  uint32_t clobber_value = rnd_uint32();
  for (size_t i = 0; i < ARRAYSIZE(boot_measurements.rom_ext.data); ++i) {
    boot_measurements.rom_ext.data[i] = clobber_value;
  }
  hmac_sha256_init();
  // Invalidate the digest if the security version of the manifest is smaller
  // than the minimum required security version.
  if (launder32(manifest->security_version) <
      boot_data.min_security_version_rom_ext) {
    uint32_t extra_word = UINT32_MAX;
    hmac_sha256_update(&extra_word, sizeof(extra_word));
  }
  HARDENED_CHECK_GE(manifest->security_version,
                    boot_data.min_security_version_rom_ext);

  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits,
                                  &usage_constraints_from_hw);
  hmac_sha256_update(&usage_constraints_from_hw,
                     sizeof(usage_constraints_from_hw));
  // Hash the remaining part of the image.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);
  hmac_sha256_update(digest_region.start, digest_region.length);
  // Verify signature
  hmac_digest_t act_digest;
  hmac_sha256_final(&act_digest);

  static_assert(sizeof(boot_measurements.rom_ext) == sizeof(act_digest),
                "Unexpected ROM_EXT digest size.");
  memcpy(&boot_measurements.rom_ext, &act_digest,
         sizeof(boot_measurements.rom_ext));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 2);
  return sigverify_rsa_verify(&manifest->signature, key, &act_digest, lc_state,
                              flash_exec);
}

/* These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom/rom.ld`, and describes the
 * location of the flash header.
 */
extern char _rom_ext_virtual_start_address[];
extern char _rom_ext_virtual_size[];
/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
static inline uintptr_t rom_ext_vma_get(const manifest_t *manifest,
                                        uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_rom_ext_virtual_start_address);
}

/**
 * Performs consistency checks before booting a ROM_EXT.
 *
 * All of the checks in this function are expected to pass and any failures
 * result in shutdown.
 */
static void rom_pre_boot_check(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 1);

  // Check the alert_handler configuration.
  SHUTDOWN_IF_ERROR(alert_config_check(lc_state));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 2);

  // Check cached life cycle state against the value reported by hardware.
  lifecycle_state_t lc_state_check = lifecycle_state_get();
  if (launder32(lc_state_check) != lc_state) {
    HARDENED_UNREACHABLE();
  }
  HARDENED_CHECK_EQ(lc_state_check, lc_state);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 3);

  // Check cached boot data.
  rom_error_t boot_data_ok = boot_data_check(&boot_data);
  if (launder32(boot_data_ok) != kErrorOk) {
    HARDENED_UNREACHABLE();
  }
  HARDENED_CHECK_EQ(boot_data_ok, kErrorOk);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 4);

  // Check the cpuctrl CSR.
  uint32_t cpuctrl_csr;
  uint32_t cpuctrl_otp =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET);
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  // We only mask the 8th bit (`ic_scr_key_valid`) to include exception flags
  // (bits 6 and 7) in the check.
  cpuctrl_csr = bitfield_bit32_write(cpuctrl_csr, 8, false);
  if (launder32(cpuctrl_csr) != cpuctrl_otp) {
    HARDENED_UNREACHABLE();
  }
  HARDENED_CHECK_EQ(cpuctrl_csr, cpuctrl_otp);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 5);

  sec_mmio_check_counters(/*expected_check_count=*/3);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 6);
}

/**
 * Boots a ROM_EXT.
 *
 * Note: This function should not return under normal conditions. Any returns
 * from this function must result in shutdown.
 *
 * @param manifest Manifest of the ROM_EXT to boot.
 * @param flash_exec Value to write to the flash_ctrl EXEC register.
 * @return rom_error_t Result of the operation.
 */
static rom_error_t rom_boot(const manifest_t *manifest, uint32_t flash_exec) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 1);
  HARDENED_RETURN_IF_ERROR(keymgr_state_check(kKeymgrStateReset));

  const keymgr_binding_value_t *attestation_measurement =
      &manifest->binding_value;
  uint32_t use_rom_ext_measurement =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN_OFFSET);
  if (launder32(use_rom_ext_measurement) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(use_rom_ext_measurement, kHardenedBoolTrue);
    attestation_measurement =
        (const keymgr_binding_value_t *)&boot_measurements.rom_ext;
  } else {
    HARDENED_CHECK_NE(use_rom_ext_measurement, kHardenedBoolTrue);
  }
  keymgr_sw_binding_set(&manifest->binding_value, attestation_measurement);
  keymgr_creator_max_ver_set(manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet +
                           kKeymgrSecMmioCreatorMaxVerSet);

  sec_mmio_check_counters(/*expected_check_count=*/2);

  // Configure address translation, compute the epmp regions and the entry
  // point for the virtual address in case the address translation is enabled.
  // Otherwise, compute the epmp regions and the entry point for the load
  // address.
  epmp_region_t text_region = manifest_code_region_get(manifest);
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  switch (launder32(manifest->address_translation)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolTrue);
      ibex_addr_remap_0_set((uintptr_t)_rom_ext_virtual_start_address,
                            (uintptr_t)manifest, (size_t)_rom_ext_virtual_size);
      SEC_MMIO_WRITE_INCREMENT(kAddressTranslationSecMmioConfigure);

      // Unlock read-only for the whole rom_ext virtual memory.
      HARDENED_RETURN_IF_ERROR(epmp_state_check());
      rom_epmp_unlock_rom_ext_r(
          (epmp_region_t){.start = (uintptr_t)_rom_ext_virtual_start_address,
                          .end = (uintptr_t)_rom_ext_virtual_start_address +
                                 (uintptr_t)_rom_ext_virtual_size});

      // Move the ROM_EXT execution section from the load address to the virtual
      // address.
      text_region.start = rom_ext_vma_get(manifest, text_region.start);
      text_region.end = rom_ext_vma_get(manifest, text_region.end);
      entry_point = rom_ext_vma_get(manifest, entry_point);
      break;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolFalse);
      break;
    default:
      HARDENED_UNREACHABLE();
  }

  // Unlock execution of ROM_EXT executable code (text) sections.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  rom_epmp_unlock_rom_ext_rx(text_region);
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomBoot, 2, kCfiRomPreBootCheck);
  rom_pre_boot_check();
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 4);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomPreBootCheck, 7);

  // Enable execution of code from flash if signature is verified.
  flash_ctrl_exec_set(flash_exec);
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioExecSet);

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/5);

  // Jump to ROM_EXT entry point.
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 5);
  ((rom_ext_entry_point *)entry_point)();

  return kErrorRomBootFailed;
}

/**
 * Attempts to boot ROM_EXTs in the order given by the boot policy module.
 *
 * @return Result of the last attempt.
 */
static rom_error_t rom_try_boot(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 1);

  // Read boot data from flash
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, &boot_data));

  boot_policy_manifests_t manifests = boot_policy_manifests_get();
  uint32_t flash_exec = 0;

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 2, kCfiRomVerify);
  rom_error_t error = rom_verify(manifests.ordered[0], &flash_exec);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 4);

  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);
    CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomTryBoot);
    CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 1, kCfiRomBoot);
    HARDENED_RETURN_IF_ERROR(rom_boot(manifests.ordered[0], flash_exec));
    return kErrorRomBootFailed;
  }
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 5, kCfiRomVerify);
  HARDENED_RETURN_IF_ERROR(rom_verify(manifests.ordered[1], &flash_exec));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 7);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 8, kCfiRomBoot);
  HARDENED_RETURN_IF_ERROR(rom_boot(manifests.ordered[1], flash_exec));
  return kErrorRomBootFailed;
}

void rom_main(void) {
  int * pad_bootmode;
  pad_bootmode = (int *)0xff000014;

  // Device init performance counters
  CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomMain);
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 1, kCfiRomInit);
  // Device initialization
  SHUTDOWN_IF_ERROR(rom_init());
  
  // Populate embedded emulated Flash (bank 0)
  if(*pad_bootmode == 0x1)
    spi_flash_load_data();
  
  //rom_bootstrap_message();
  
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomMain, 3);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomInit, 3);

  hardened_bool_t bootstrap_req = bootstrap_requested();
  if (launder32(bootstrap_req) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(bootstrap_req, kHardenedBoolTrue);
    //rom_bootstrap_message();
    watchdog_disable();
    shutdown_finalize(bootstrap());
  }

  // `rom_try_boot` will not return unless there is an error.
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 4, kCfiRomTryBoot);
  

  shutdown_finalize(rom_try_boot());
}

void rom_interrupt_handler(void) {
  register rom_error_t error asm("a0") = rom_irq_error();
  asm volatile("tail shutdown_finalize;" ::"r"(error));
  OT_UNREACHABLE();
}

// We only need a single handler for all ROM interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the ROM,
// alias all interrupt handler symbols to the single handler.
OT_ALIAS("rom_interrupt_handler")
noreturn void rom_exception_handler(void);

OT_ALIAS("rom_interrupt_handler")
noreturn void rom_nmi_handler(void);
