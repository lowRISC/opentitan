
#include "alsaqr_periph_padframe.h"
#define  ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG0_BASE_ADDR ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS
#include "alsaqr_periph_padframe_periphs_regs.h"
#include "bitfield.h"

#define REG_WRITE32(addr, value) *((volatile uint32_t*) addr) = (uint32_t) value
#define REG_READ32(addr) *((volatile uint32_t*) addr)


void alsaqr_periph_padframe_periphs_a_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_00_mux_set(alsaqr_periph_padframe_periphs_a_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_00_mux_sel_t alsaqr_periph_padframe_periphs_a_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_01_mux_set(alsaqr_periph_padframe_periphs_a_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_01_mux_sel_t alsaqr_periph_padframe_periphs_a_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_02_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_02_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_02_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_02_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_02_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_02_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_02_mux_set(alsaqr_periph_padframe_periphs_a_02_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_02_mux_sel_t alsaqr_periph_padframe_periphs_a_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_03_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_03_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_03_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_03_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_03_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_03_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_03_mux_set(alsaqr_periph_padframe_periphs_a_03_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_03_mux_sel_t alsaqr_periph_padframe_periphs_a_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_04_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_04_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_04_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_04_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_04_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_04_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_04_mux_set(alsaqr_periph_padframe_periphs_a_04_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_04_mux_sel_t alsaqr_periph_padframe_periphs_a_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_05_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_05_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_05_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_05_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_05_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_05_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_05_mux_set(alsaqr_periph_padframe_periphs_a_05_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_05_mux_sel_t alsaqr_periph_padframe_periphs_a_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_06_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_06_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_06_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_06_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_06_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_06_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_06_mux_set(alsaqr_periph_padframe_periphs_a_06_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_06_mux_sel_t alsaqr_periph_padframe_periphs_a_06_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_07_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_07_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_07_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_07_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_07_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_07_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_07_mux_set(alsaqr_periph_padframe_periphs_a_07_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_07_mux_sel_t alsaqr_periph_padframe_periphs_a_07_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_08_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_08_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_08_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_08_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_08_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_08_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_08_mux_set(alsaqr_periph_padframe_periphs_a_08_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_08_mux_sel_t alsaqr_periph_padframe_periphs_a_08_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_09_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_09_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_09_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_09_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_09_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_09_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_09_mux_set(alsaqr_periph_padframe_periphs_a_09_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_09_mux_sel_t alsaqr_periph_padframe_periphs_a_09_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_10_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_10_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_10_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_10_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_10_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_10_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_10_mux_set(alsaqr_periph_padframe_periphs_a_10_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_10_mux_sel_t alsaqr_periph_padframe_periphs_a_10_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_11_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_11_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_11_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_11_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_11_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_11_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_11_mux_set(alsaqr_periph_padframe_periphs_a_11_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_11_mux_sel_t alsaqr_periph_padframe_periphs_a_11_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_12_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_12_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_12_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_12_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_12_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_12_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_12_mux_set(alsaqr_periph_padframe_periphs_a_12_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_12_mux_sel_t alsaqr_periph_padframe_periphs_a_12_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_13_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_13_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_13_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_13_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_13_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_13_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_13_mux_set(alsaqr_periph_padframe_periphs_a_13_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_13_mux_sel_t alsaqr_periph_padframe_periphs_a_13_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_14_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_14_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_14_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_14_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_14_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_14_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_14_mux_set(alsaqr_periph_padframe_periphs_a_14_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_14_mux_sel_t alsaqr_periph_padframe_periphs_a_14_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_15_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_15_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_15_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_15_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_15_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_15_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_15_mux_set(alsaqr_periph_padframe_periphs_a_15_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_15_mux_sel_t alsaqr_periph_padframe_periphs_a_15_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_16_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_16_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_16_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_16_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_16_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_16_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_16_mux_set(alsaqr_periph_padframe_periphs_a_16_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_16_mux_sel_t alsaqr_periph_padframe_periphs_a_16_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_17_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_17_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_17_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_17_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_17_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_17_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_17_mux_set(alsaqr_periph_padframe_periphs_a_17_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_17_mux_sel_t alsaqr_periph_padframe_periphs_a_17_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_18_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_18_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_18_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_18_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_18_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_18_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_18_mux_set(alsaqr_periph_padframe_periphs_a_18_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_18_mux_sel_t alsaqr_periph_padframe_periphs_a_18_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_19_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_19_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_19_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_19_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_19_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_19_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_19_mux_set(alsaqr_periph_padframe_periphs_a_19_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_19_mux_sel_t alsaqr_periph_padframe_periphs_a_19_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_20_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_20_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_20_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_20_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_20_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_20_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_20_mux_set(alsaqr_periph_padframe_periphs_a_20_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_20_mux_sel_t alsaqr_periph_padframe_periphs_a_20_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_21_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_21_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_21_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_21_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_21_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_21_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_21_mux_set(alsaqr_periph_padframe_periphs_a_21_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_21_mux_sel_t alsaqr_periph_padframe_periphs_a_21_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_22_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_22_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_22_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_22_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_22_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_22_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_22_mux_set(alsaqr_periph_padframe_periphs_a_22_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_22_mux_sel_t alsaqr_periph_padframe_periphs_a_22_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_23_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_23_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_23_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_23_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_23_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_23_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_23_mux_set(alsaqr_periph_padframe_periphs_a_23_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_23_mux_sel_t alsaqr_periph_padframe_periphs_a_23_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_24_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_24_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_24_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_24_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_24_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_24_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_24_mux_set(alsaqr_periph_padframe_periphs_a_24_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_24_mux_sel_t alsaqr_periph_padframe_periphs_a_24_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_25_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_25_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_25_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_25_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_25_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_25_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_25_mux_set(alsaqr_periph_padframe_periphs_a_25_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_25_mux_sel_t alsaqr_periph_padframe_periphs_a_25_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_26_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_26_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_26_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_26_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_26_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_26_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_26_mux_set(alsaqr_periph_padframe_periphs_a_26_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_26_mux_sel_t alsaqr_periph_padframe_periphs_a_26_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_27_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_27_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_27_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_27_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_27_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_27_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_27_mux_set(alsaqr_periph_padframe_periphs_a_27_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_27_mux_sel_t alsaqr_periph_padframe_periphs_a_27_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_28_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_28_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_28_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_28_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_28_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_28_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_28_mux_set(alsaqr_periph_padframe_periphs_a_28_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_28_mux_sel_t alsaqr_periph_padframe_periphs_a_28_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_29_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_29_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_29_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_29_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_29_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_29_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_29_mux_set(alsaqr_periph_padframe_periphs_a_29_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_29_mux_sel_t alsaqr_periph_padframe_periphs_a_29_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_00_mux_set(alsaqr_periph_padframe_periphs_b_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_00_mux_sel_t alsaqr_periph_padframe_periphs_b_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_01_mux_set(alsaqr_periph_padframe_periphs_b_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_01_mux_sel_t alsaqr_periph_padframe_periphs_b_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_02_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_02_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_02_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_02_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_02_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_02_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_02_mux_set(alsaqr_periph_padframe_periphs_b_02_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_02_mux_sel_t alsaqr_periph_padframe_periphs_b_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_03_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_03_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_03_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_03_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_03_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_03_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_03_mux_set(alsaqr_periph_padframe_periphs_b_03_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_03_mux_sel_t alsaqr_periph_padframe_periphs_b_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_04_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_04_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_04_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_04_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_04_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_04_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_04_mux_set(alsaqr_periph_padframe_periphs_b_04_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_04_mux_sel_t alsaqr_periph_padframe_periphs_b_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_05_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_05_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_05_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_05_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_05_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_05_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_05_mux_set(alsaqr_periph_padframe_periphs_b_05_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_05_mux_sel_t alsaqr_periph_padframe_periphs_b_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_06_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_06_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_06_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_06_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_06_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_06_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_06_mux_set(alsaqr_periph_padframe_periphs_b_06_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_06_mux_sel_t alsaqr_periph_padframe_periphs_b_06_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_07_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_07_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_07_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_07_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_07_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_07_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_07_mux_set(alsaqr_periph_padframe_periphs_b_07_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_07_mux_sel_t alsaqr_periph_padframe_periphs_b_07_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_08_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_08_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_08_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_08_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_08_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_08_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_08_mux_set(alsaqr_periph_padframe_periphs_b_08_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_08_mux_sel_t alsaqr_periph_padframe_periphs_b_08_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_09_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_09_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_09_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_09_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_09_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_09_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_09_mux_set(alsaqr_periph_padframe_periphs_b_09_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_09_mux_sel_t alsaqr_periph_padframe_periphs_b_09_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_10_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_10_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_10_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_10_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_10_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_10_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_10_mux_set(alsaqr_periph_padframe_periphs_b_10_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_10_mux_sel_t alsaqr_periph_padframe_periphs_b_10_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_11_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_11_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_11_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_11_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_11_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_11_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_11_mux_set(alsaqr_periph_padframe_periphs_b_11_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_11_mux_sel_t alsaqr_periph_padframe_periphs_b_11_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_12_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_12_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_12_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_12_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_12_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_12_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_12_mux_set(alsaqr_periph_padframe_periphs_b_12_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_12_mux_sel_t alsaqr_periph_padframe_periphs_b_12_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_13_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_13_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_13_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_13_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_13_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_13_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_13_mux_set(alsaqr_periph_padframe_periphs_b_13_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_13_mux_sel_t alsaqr_periph_padframe_periphs_b_13_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_14_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_14_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_14_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_14_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_14_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_14_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_14_mux_set(alsaqr_periph_padframe_periphs_b_14_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_14_mux_sel_t alsaqr_periph_padframe_periphs_b_14_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_15_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_15_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_15_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_15_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_15_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_15_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_15_mux_set(alsaqr_periph_padframe_periphs_b_15_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_15_mux_sel_t alsaqr_periph_padframe_periphs_b_15_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_16_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_16_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_16_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_16_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_16_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_16_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_16_mux_set(alsaqr_periph_padframe_periphs_b_16_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_16_mux_sel_t alsaqr_periph_padframe_periphs_b_16_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_17_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_17_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_17_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_17_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_17_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_17_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_17_mux_set(alsaqr_periph_padframe_periphs_b_17_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_17_mux_sel_t alsaqr_periph_padframe_periphs_b_17_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_18_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_18_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_18_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_18_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_18_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_18_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_18_mux_set(alsaqr_periph_padframe_periphs_b_18_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_18_mux_sel_t alsaqr_periph_padframe_periphs_b_18_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_19_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_19_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_19_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_19_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_19_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_19_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_19_mux_set(alsaqr_periph_padframe_periphs_b_19_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_19_mux_sel_t alsaqr_periph_padframe_periphs_b_19_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_20_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_20_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_20_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_20_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_20_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_20_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_20_mux_set(alsaqr_periph_padframe_periphs_b_20_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_20_mux_sel_t alsaqr_periph_padframe_periphs_b_20_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_21_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_21_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_21_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_21_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_21_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_21_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_21_mux_set(alsaqr_periph_padframe_periphs_b_21_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_21_mux_sel_t alsaqr_periph_padframe_periphs_b_21_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_22_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_22_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_22_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_22_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_22_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_22_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_22_mux_set(alsaqr_periph_padframe_periphs_b_22_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_22_mux_sel_t alsaqr_periph_padframe_periphs_b_22_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_23_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_23_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_23_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_23_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_23_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_23_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_23_mux_set(alsaqr_periph_padframe_periphs_b_23_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_23_mux_sel_t alsaqr_periph_padframe_periphs_b_23_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_24_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_24_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_24_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_24_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_24_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_24_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_24_mux_set(alsaqr_periph_padframe_periphs_b_24_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_24_mux_sel_t alsaqr_periph_padframe_periphs_b_24_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_25_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_25_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_25_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_25_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_25_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_25_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_25_mux_set(alsaqr_periph_padframe_periphs_b_25_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_25_mux_sel_t alsaqr_periph_padframe_periphs_b_25_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_26_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_26_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_26_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_26_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_26_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_26_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_26_mux_set(alsaqr_periph_padframe_periphs_b_26_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_26_mux_sel_t alsaqr_periph_padframe_periphs_b_26_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_27_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_27_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_27_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_27_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_27_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_27_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_27_mux_set(alsaqr_periph_padframe_periphs_b_27_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_27_mux_sel_t alsaqr_periph_padframe_periphs_b_27_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_28_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_28_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_28_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_28_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_28_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_28_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_28_mux_set(alsaqr_periph_padframe_periphs_b_28_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_28_mux_sel_t alsaqr_periph_padframe_periphs_b_28_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_29_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_29_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_29_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_29_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_29_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_29_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_29_mux_set(alsaqr_periph_padframe_periphs_b_29_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_29_mux_sel_t alsaqr_periph_padframe_periphs_b_29_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_30_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_30_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_30_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_30_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_30_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_30_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_30_mux_set(alsaqr_periph_padframe_periphs_b_30_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_30_mux_sel_t alsaqr_periph_padframe_periphs_b_30_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_31_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_31_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_31_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_31_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_31_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_31_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_31_mux_set(alsaqr_periph_padframe_periphs_b_31_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_31_mux_sel_t alsaqr_periph_padframe_periphs_b_31_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_32_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_32_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_32_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_32_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_32_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_32_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_32_mux_set(alsaqr_periph_padframe_periphs_b_32_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_32_mux_sel_t alsaqr_periph_padframe_periphs_b_32_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_33_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_33_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_33_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_33_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_33_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_33_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_33_mux_set(alsaqr_periph_padframe_periphs_b_33_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_33_mux_sel_t alsaqr_periph_padframe_periphs_b_33_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 3;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_34_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_34_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_34_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_34_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_34_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_34_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_34_mux_set(alsaqr_periph_padframe_periphs_b_34_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_34_mux_sel_t alsaqr_periph_padframe_periphs_b_34_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_35_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_35_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_35_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_35_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_35_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_35_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_35_mux_set(alsaqr_periph_padframe_periphs_b_35_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_35_mux_sel_t alsaqr_periph_padframe_periphs_b_35_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_36_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_36_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_36_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_36_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_36_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_36_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_36_mux_set(alsaqr_periph_padframe_periphs_b_36_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_36_mux_sel_t alsaqr_periph_padframe_periphs_b_36_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_37_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_37_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_37_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_37_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_37_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_37_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_37_mux_set(alsaqr_periph_padframe_periphs_b_37_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_37_mux_sel_t alsaqr_periph_padframe_periphs_b_37_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_38_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_38_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_38_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_38_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_38_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_38_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_38_mux_set(alsaqr_periph_padframe_periphs_b_38_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_38_mux_sel_t alsaqr_periph_padframe_periphs_b_38_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_39_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_39_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_39_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_39_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_39_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_39_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_39_mux_set(alsaqr_periph_padframe_periphs_b_39_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_39_mux_sel_t alsaqr_periph_padframe_periphs_b_39_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_40_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_40_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_40_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_40_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_40_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_40_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_40_mux_set(alsaqr_periph_padframe_periphs_b_40_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_40_mux_sel_t alsaqr_periph_padframe_periphs_b_40_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_41_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_41_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_41_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_41_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_41_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_41_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_41_mux_set(alsaqr_periph_padframe_periphs_b_41_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_41_mux_sel_t alsaqr_periph_padframe_periphs_b_41_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_42_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_42_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_42_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_42_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_42_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_42_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_42_mux_set(alsaqr_periph_padframe_periphs_b_42_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_42_mux_sel_t alsaqr_periph_padframe_periphs_b_42_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_43_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_43_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_43_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_43_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_43_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_43_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_43_mux_set(alsaqr_periph_padframe_periphs_b_43_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_43_mux_sel_t alsaqr_periph_padframe_periphs_b_43_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_44_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_44_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_44_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_44_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_44_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_44_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_44_mux_set(alsaqr_periph_padframe_periphs_b_44_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_44_mux_sel_t alsaqr_periph_padframe_periphs_b_44_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_45_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_45_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_45_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_45_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_45_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_45_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_45_mux_set(alsaqr_periph_padframe_periphs_b_45_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_45_mux_sel_t alsaqr_periph_padframe_periphs_b_45_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_46_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_46_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_46_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_46_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_46_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_46_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_46_mux_set(alsaqr_periph_padframe_periphs_b_46_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_46_mux_sel_t alsaqr_periph_padframe_periphs_b_46_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_47_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_47_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_47_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_47_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_47_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_47_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_47_mux_set(alsaqr_periph_padframe_periphs_b_47_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_47_mux_sel_t alsaqr_periph_padframe_periphs_b_47_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_47_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_00_mux_set(alsaqr_periph_padframe_periphs_ot_spi_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_spi_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_01_mux_set(alsaqr_periph_padframe_periphs_ot_spi_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_spi_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_02_mux_set(alsaqr_periph_padframe_periphs_ot_spi_02_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_spi_02_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_spi_03_mux_set(alsaqr_periph_padframe_periphs_ot_spi_03_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_spi_03_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_SPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}
