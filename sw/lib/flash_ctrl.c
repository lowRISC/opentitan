// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "flash_ctrl.h"

#include <stdint.h>

#include "common.h"

static uint32_t get_clr_err(void) {
  uint32_t err_status;

  // extract error status
  err_status =
      REG32(FLASH_CTRL_INTR_STATE(0)) & (0x1 << FLASH_CTRL_INTR_STATE_OP_ERROR);

  // clear error if set
  REG32(FLASH_CTRL_INTR_STATE(0)) = err_status;

  // return status
  return err_status;
}

// flash initialization done
void wait_flash_init(void) {
  while ((REG32(FLASH_CTRL_STATUS(0)) & (1 << FLASH_CTRL_STATUS_INIT_WIP)) >
         0) {
  }
}

// wait for flash done and ack
void wait_done_and_ack(void) {
  while ((REG32(FLASH_CTRL_OP_STATUS(0)) & (1 << FLASH_CTRL_OP_STATUS_DONE)) ==
         0)
    ;

  REG32(FLASH_CTRL_OP_STATUS(0)) = 0;
}

// setup flash prog
void setup_flash_prog(uint32_t addr, uint32_t num) {
  uint32_t val;

  val = FlashProg << FLASH_CTRL_CONTROL_OP_OFFSET |
        (num - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
        0x1 << FLASH_CTRL_CONTROL_START;

  REG32(FLASH_CTRL_ADDR(0)) = addr;

  REG32(FLASH_CTRL_CONTROL(0)) = val;
}

// program data
uint32_t prog_flash(uint32_t addr, uint32_t num, uint32_t *data) {
  uint32_t i = 0;

  // setup flash programming
  setup_flash_prog(addr, num);

  // beginning filling up the fifo
  for (i = 0; i < num; i++) {
    REG32(FLASH_CTRL_PROG_FIFO(0)) = *data;
    data++;
  }

  // wait for operation finish
  wait_done_and_ack();

  // return error status
  return get_clr_err();
}

// read data
uint32_t read_flash(uint32_t addr, uint32_t num, uint32_t *data) {
  uint32_t val;
  uint32_t i = 0;

  // kick off flash operation
  val = FlashRead << FLASH_CTRL_CONTROL_OP_OFFSET |
        (num - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
        0x1 << FLASH_CTRL_CONTROL_START;

  REG32(FLASH_CTRL_ADDR(0)) = addr;

  REG32(FLASH_CTRL_CONTROL(0)) = val;

  while (i < num) {
    // if not empty, read a word
    if (((REG32(FLASH_CTRL_STATUS(0)) >> FLASH_CTRL_STATUS_RD_EMPTY) & 0x1) ==
        0) {
      *data++ = REG32(FLASH_CTRL_RD_FIFO(0));
      i++;
    }
  }

  // wait for operation finish
  wait_done_and_ack();

  // return error status
  return get_clr_err();
}

// page erase flash
// wrap down to closest down to page boundary
uint32_t page_erase(uint32_t addr) {
  uint32_t val;
  uint32_t data[ERASE_CHECK_WORDS];
  uint32_t verify_rounds;
  uint32_t error;

  error = 0;
  verify_rounds = WORDS_PER_PAGE / ERASE_CHECK_WORDS;

  // kick off flash operation
  val = FlashErase << FLASH_CTRL_CONTROL_OP_OFFSET |
        PageErase << FLASH_CTRL_CONTROL_ERASE_SEL |
        0x1 << FLASH_CTRL_CONTROL_START;

  REG32(FLASH_CTRL_ADDR(0)) = addr;

  REG32(FLASH_CTRL_CONTROL(0)) = val;

  // wait for operation finish
  wait_done_and_ack();

  error += get_clr_err();

  // verify erase
  for (uint32_t i = 0; i < verify_rounds; i++) {
    error += read_flash(addr + i * ERASE_CHECK_WORDS * BYTES_PER_WORD,
                        ERASE_CHECK_WORDS, data);

    for (uint32_t j = 0; j < ERASE_CHECK_WORDS; j++) {
      if (data[i] != 0xFFFFFFFF) {
        REG32(FLASH_CTRL_SCRATCH(0)) = data[i];

        // re-init array
        data[i] = 0;
        error++;
      }
    }
  }

  // return error status
  return error;
}

void flash_default_region(uint32_t rd_en, uint32_t prog_en, uint32_t erase_en) {
  REG32(FLASH_CTRL_DEFAULT_REGION(0)) =
      rd_en << FLASH_CTRL_DEFAULT_REGION_RD_EN |
      prog_en << FLASH_CTRL_DEFAULT_REGION_PROG_EN |
      erase_en << FLASH_CTRL_DEFAULT_REGION_ERASE_EN;
}

void flash_cfg_region(mp_region_t region_cfg) {
  REG32(FLASH_CTRL_MP_REGION_CFG0(0) + region_cfg.num * 4) =
      region_cfg.base << FLASH_CTRL_MP_REGION_CFG0_BASE0_OFFSET |
      region_cfg.size << FLASH_CTRL_MP_REGION_CFG0_SIZE0_OFFSET |
      region_cfg.rd_en << FLASH_CTRL_MP_REGION_CFG0_RD_EN0 |
      region_cfg.prog_en << FLASH_CTRL_MP_REGION_CFG0_PROG_EN0 |
      region_cfg.erase_en << FLASH_CTRL_MP_REGION_CFG0_ERASE_EN0 |
      0x1 << FLASH_CTRL_MP_REGION_CFG0_EN0;
}
