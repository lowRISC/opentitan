
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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_00_mux_sel_t alsaqr_periph_padframe_periphs_a_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_01_mux_sel_t alsaqr_periph_padframe_periphs_a_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_02_mux_sel_t alsaqr_periph_padframe_periphs_a_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_03_mux_sel_t alsaqr_periph_padframe_periphs_a_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_04_mux_sel_t alsaqr_periph_padframe_periphs_a_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_05_mux_sel_t alsaqr_periph_padframe_periphs_a_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_06_mux_sel_t alsaqr_periph_padframe_periphs_a_06_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_07_mux_sel_t alsaqr_periph_padframe_periphs_a_07_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_08_mux_sel_t alsaqr_periph_padframe_periphs_a_08_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_09_mux_sel_t alsaqr_periph_padframe_periphs_a_09_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_10_mux_sel_t alsaqr_periph_padframe_periphs_a_10_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_11_mux_sel_t alsaqr_periph_padframe_periphs_a_11_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_12_mux_sel_t alsaqr_periph_padframe_periphs_a_12_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_13_mux_sel_t alsaqr_periph_padframe_periphs_a_13_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_14_mux_sel_t alsaqr_periph_padframe_periphs_a_14_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_15_mux_sel_t alsaqr_periph_padframe_periphs_a_15_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_16_mux_sel_t alsaqr_periph_padframe_periphs_a_16_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_17_mux_sel_t alsaqr_periph_padframe_periphs_a_17_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_18_mux_sel_t alsaqr_periph_padframe_periphs_a_18_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_19_mux_sel_t alsaqr_periph_padframe_periphs_a_19_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_20_mux_sel_t alsaqr_periph_padframe_periphs_a_20_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_21_mux_sel_t alsaqr_periph_padframe_periphs_a_21_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_22_mux_sel_t alsaqr_periph_padframe_periphs_a_22_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_23_mux_sel_t alsaqr_periph_padframe_periphs_a_23_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_24_mux_sel_t alsaqr_periph_padframe_periphs_a_24_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_25_mux_sel_t alsaqr_periph_padframe_periphs_a_25_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_26_mux_sel_t alsaqr_periph_padframe_periphs_a_26_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_27_mux_sel_t alsaqr_periph_padframe_periphs_a_27_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_28_mux_sel_t alsaqr_periph_padframe_periphs_a_28_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_29_mux_sel_t alsaqr_periph_padframe_periphs_a_29_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_30_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_30_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_30_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_30_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_30_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_30_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_30_mux_set(alsaqr_periph_padframe_periphs_a_30_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_30_mux_sel_t alsaqr_periph_padframe_periphs_a_30_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_30_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_31_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_31_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_31_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_31_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_31_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_31_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_31_mux_set(alsaqr_periph_padframe_periphs_a_31_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_31_mux_sel_t alsaqr_periph_padframe_periphs_a_31_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_31_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_32_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_32_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_32_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_32_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_32_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_32_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_32_mux_set(alsaqr_periph_padframe_periphs_a_32_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_32_mux_sel_t alsaqr_periph_padframe_periphs_a_32_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_32_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_33_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_33_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_33_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_33_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_33_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_33_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_33_mux_set(alsaqr_periph_padframe_periphs_a_33_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_33_mux_sel_t alsaqr_periph_padframe_periphs_a_33_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_33_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_34_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_34_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_34_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_34_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_34_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_34_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_34_mux_set(alsaqr_periph_padframe_periphs_a_34_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_34_mux_sel_t alsaqr_periph_padframe_periphs_a_34_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_34_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_35_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_35_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_35_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_35_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_35_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_35_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_35_mux_set(alsaqr_periph_padframe_periphs_a_35_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_35_mux_sel_t alsaqr_periph_padframe_periphs_a_35_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_35_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_36_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_36_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_36_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_36_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_36_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_36_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_36_mux_set(alsaqr_periph_padframe_periphs_a_36_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_36_mux_sel_t alsaqr_periph_padframe_periphs_a_36_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_36_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_37_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_37_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_37_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_37_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_37_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_37_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_37_mux_set(alsaqr_periph_padframe_periphs_a_37_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_37_mux_sel_t alsaqr_periph_padframe_periphs_a_37_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_37_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_38_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_38_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_38_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_38_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_38_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_38_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_38_mux_set(alsaqr_periph_padframe_periphs_a_38_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_38_mux_sel_t alsaqr_periph_padframe_periphs_a_38_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_38_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_39_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_39_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_39_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_39_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_39_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_39_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_39_mux_set(alsaqr_periph_padframe_periphs_a_39_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_39_mux_sel_t alsaqr_periph_padframe_periphs_a_39_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_39_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_40_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_40_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_40_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_40_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_40_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_40_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_40_mux_set(alsaqr_periph_padframe_periphs_a_40_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_40_mux_sel_t alsaqr_periph_padframe_periphs_a_40_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_40_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_41_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_41_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_41_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_41_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_41_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_41_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_41_mux_set(alsaqr_periph_padframe_periphs_a_41_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_41_mux_sel_t alsaqr_periph_padframe_periphs_a_41_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_41_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_42_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_42_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_42_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_42_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_42_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_42_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_42_mux_set(alsaqr_periph_padframe_periphs_a_42_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_42_mux_sel_t alsaqr_periph_padframe_periphs_a_42_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_42_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_43_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_43_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_43_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_43_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_43_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_43_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_43_mux_set(alsaqr_periph_padframe_periphs_a_43_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_43_mux_sel_t alsaqr_periph_padframe_periphs_a_43_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_43_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_44_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_44_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_44_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_44_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_44_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_44_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_44_mux_set(alsaqr_periph_padframe_periphs_a_44_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_44_mux_sel_t alsaqr_periph_padframe_periphs_a_44_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_44_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_45_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_45_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_45_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_45_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_45_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_45_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_45_mux_set(alsaqr_periph_padframe_periphs_a_45_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_45_mux_sel_t alsaqr_periph_padframe_periphs_a_45_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_45_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_46_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_46_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_46_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_46_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_46_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_46_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_46_mux_set(alsaqr_periph_padframe_periphs_a_46_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_46_mux_sel_t alsaqr_periph_padframe_periphs_a_46_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_46_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_47_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_47_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_47_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_47_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_47_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_47_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_47_mux_set(alsaqr_periph_padframe_periphs_a_47_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_47_mux_sel_t alsaqr_periph_padframe_periphs_a_47_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_47_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_48_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_48_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_48_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_48_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_48_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_48_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_48_mux_set(alsaqr_periph_padframe_periphs_a_48_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_48_mux_sel_t alsaqr_periph_padframe_periphs_a_48_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_48_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_49_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_49_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_49_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_49_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_49_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_49_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_49_mux_set(alsaqr_periph_padframe_periphs_a_49_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_49_mux_sel_t alsaqr_periph_padframe_periphs_a_49_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_49_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_50_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_50_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_50_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_50_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_50_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_50_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_50_mux_set(alsaqr_periph_padframe_periphs_a_50_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_50_mux_sel_t alsaqr_periph_padframe_periphs_a_50_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_50_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_51_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_51_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_51_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_51_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_51_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_51_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_51_mux_set(alsaqr_periph_padframe_periphs_a_51_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_51_mux_sel_t alsaqr_periph_padframe_periphs_a_51_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_51_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_52_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_52_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_52_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_52_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_52_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_52_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_52_mux_set(alsaqr_periph_padframe_periphs_a_52_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_52_mux_sel_t alsaqr_periph_padframe_periphs_a_52_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_52_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_53_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_53_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_53_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_53_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_53_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_53_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_53_mux_set(alsaqr_periph_padframe_periphs_a_53_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_53_mux_sel_t alsaqr_periph_padframe_periphs_a_53_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_53_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_54_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_54_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_54_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_54_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_54_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_54_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_54_mux_set(alsaqr_periph_padframe_periphs_a_54_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_54_mux_sel_t alsaqr_periph_padframe_periphs_a_54_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_54_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_55_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_55_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_55_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_55_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_55_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_55_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_55_mux_set(alsaqr_periph_padframe_periphs_a_55_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_55_mux_sel_t alsaqr_periph_padframe_periphs_a_55_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_55_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_56_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_56_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_56_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_56_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_56_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_56_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_56_mux_set(alsaqr_periph_padframe_periphs_a_56_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_56_mux_sel_t alsaqr_periph_padframe_periphs_a_56_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_56_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_57_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_57_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_57_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_57_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_57_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_57_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_57_mux_set(alsaqr_periph_padframe_periphs_a_57_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_57_mux_sel_t alsaqr_periph_padframe_periphs_a_57_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_57_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_58_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_58_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_58_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_58_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_58_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_58_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_58_mux_set(alsaqr_periph_padframe_periphs_a_58_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_58_mux_sel_t alsaqr_periph_padframe_periphs_a_58_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_58_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_59_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_59_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_59_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_59_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_59_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_59_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_59_mux_set(alsaqr_periph_padframe_periphs_a_59_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_59_mux_sel_t alsaqr_periph_padframe_periphs_a_59_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_59_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_60_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_60_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_60_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_60_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_60_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_60_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_60_mux_set(alsaqr_periph_padframe_periphs_a_60_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_60_mux_sel_t alsaqr_periph_padframe_periphs_a_60_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_60_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_61_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_61_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_61_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_61_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_61_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_61_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_61_mux_set(alsaqr_periph_padframe_periphs_a_61_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_61_mux_sel_t alsaqr_periph_padframe_periphs_a_61_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_61_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_62_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_62_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_62_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_62_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_62_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_62_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_62_mux_set(alsaqr_periph_padframe_periphs_a_62_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_62_mux_sel_t alsaqr_periph_padframe_periphs_a_62_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_62_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_63_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_63_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_63_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_63_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_63_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_63_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_63_mux_set(alsaqr_periph_padframe_periphs_a_63_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_63_mux_sel_t alsaqr_periph_padframe_periphs_a_63_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_63_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_64_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_64_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_64_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_64_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_64_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_64_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_64_mux_set(alsaqr_periph_padframe_periphs_a_64_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_64_mux_sel_t alsaqr_periph_padframe_periphs_a_64_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_64_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_65_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_65_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_65_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_65_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_65_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_65_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_65_mux_set(alsaqr_periph_padframe_periphs_a_65_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_65_mux_sel_t alsaqr_periph_padframe_periphs_a_65_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_65_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_66_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_66_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_66_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_66_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_66_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_66_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_66_mux_set(alsaqr_periph_padframe_periphs_a_66_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_66_mux_sel_t alsaqr_periph_padframe_periphs_a_66_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_66_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_67_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_67_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_67_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_67_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_67_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_67_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_67_mux_set(alsaqr_periph_padframe_periphs_a_67_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_67_mux_sel_t alsaqr_periph_padframe_periphs_a_67_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_67_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_68_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_68_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_68_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_68_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_68_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_68_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_68_mux_set(alsaqr_periph_padframe_periphs_a_68_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_68_mux_sel_t alsaqr_periph_padframe_periphs_a_68_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_68_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_69_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_69_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_69_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_69_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_69_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_69_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_69_mux_set(alsaqr_periph_padframe_periphs_a_69_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_69_mux_sel_t alsaqr_periph_padframe_periphs_a_69_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_69_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_70_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_70_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_70_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_70_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_70_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_70_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_70_mux_set(alsaqr_periph_padframe_periphs_a_70_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_70_mux_sel_t alsaqr_periph_padframe_periphs_a_70_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_70_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_71_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_71_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_71_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_71_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_71_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_71_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_71_mux_set(alsaqr_periph_padframe_periphs_a_71_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_71_mux_sel_t alsaqr_periph_padframe_periphs_a_71_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_71_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_72_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_72_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_72_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_72_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_72_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_72_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_72_mux_set(alsaqr_periph_padframe_periphs_a_72_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_72_mux_sel_t alsaqr_periph_padframe_periphs_a_72_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_72_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_73_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_73_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_73_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_73_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_73_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_73_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_73_mux_set(alsaqr_periph_padframe_periphs_a_73_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_73_mux_sel_t alsaqr_periph_padframe_periphs_a_73_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_73_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_74_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_74_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_74_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_74_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_74_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_74_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_74_mux_set(alsaqr_periph_padframe_periphs_a_74_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_74_mux_sel_t alsaqr_periph_padframe_periphs_a_74_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_74_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_75_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_75_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_75_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_75_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_75_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_75_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_75_mux_set(alsaqr_periph_padframe_periphs_a_75_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_75_mux_sel_t alsaqr_periph_padframe_periphs_a_75_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_75_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_76_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_76_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_76_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_76_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_76_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_76_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_76_mux_set(alsaqr_periph_padframe_periphs_a_76_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_76_mux_sel_t alsaqr_periph_padframe_periphs_a_76_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_76_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_77_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_77_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_77_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_77_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_77_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_77_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_77_mux_set(alsaqr_periph_padframe_periphs_a_77_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_77_mux_sel_t alsaqr_periph_padframe_periphs_a_77_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_77_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_78_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_78_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_78_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_78_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_78_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_78_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_78_mux_set(alsaqr_periph_padframe_periphs_a_78_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_78_mux_sel_t alsaqr_periph_padframe_periphs_a_78_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_78_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_79_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_79_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_79_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_79_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_79_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_79_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_79_mux_set(alsaqr_periph_padframe_periphs_a_79_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_79_mux_sel_t alsaqr_periph_padframe_periphs_a_79_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_79_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_80_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_80_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_80_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_80_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_80_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_80_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_80_mux_set(alsaqr_periph_padframe_periphs_a_80_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_80_mux_sel_t alsaqr_periph_padframe_periphs_a_80_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_80_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_81_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_81_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_81_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_81_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_81_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_81_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_81_mux_set(alsaqr_periph_padframe_periphs_a_81_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_81_mux_sel_t alsaqr_periph_padframe_periphs_a_81_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_81_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_82_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_82_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_82_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_82_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_82_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_82_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_82_mux_set(alsaqr_periph_padframe_periphs_a_82_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_82_mux_sel_t alsaqr_periph_padframe_periphs_a_82_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_82_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_83_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_83_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_83_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_83_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_83_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_83_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_83_mux_set(alsaqr_periph_padframe_periphs_a_83_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_83_mux_sel_t alsaqr_periph_padframe_periphs_a_83_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_83_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_84_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_84_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_84_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_84_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_84_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_84_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_84_mux_set(alsaqr_periph_padframe_periphs_a_84_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_84_mux_sel_t alsaqr_periph_padframe_periphs_a_84_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_84_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_85_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_85_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_85_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_85_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_85_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_85_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_85_mux_set(alsaqr_periph_padframe_periphs_a_85_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_85_mux_sel_t alsaqr_periph_padframe_periphs_a_85_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_85_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_86_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_86_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_86_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_86_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_86_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_86_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_86_mux_set(alsaqr_periph_padframe_periphs_a_86_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_86_mux_sel_t alsaqr_periph_padframe_periphs_a_86_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_86_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_87_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_87_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_87_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_87_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_87_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_87_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_87_mux_set(alsaqr_periph_padframe_periphs_a_87_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_87_mux_sel_t alsaqr_periph_padframe_periphs_a_87_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_87_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_88_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_88_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_88_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_88_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_88_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_88_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_88_mux_set(alsaqr_periph_padframe_periphs_a_88_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_88_mux_sel_t alsaqr_periph_padframe_periphs_a_88_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_88_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_89_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_89_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_89_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_89_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_89_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_89_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_89_mux_set(alsaqr_periph_padframe_periphs_a_89_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_89_mux_sel_t alsaqr_periph_padframe_periphs_a_89_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_89_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_90_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_90_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_90_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_90_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_90_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_90_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_90_mux_set(alsaqr_periph_padframe_periphs_a_90_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_90_mux_sel_t alsaqr_periph_padframe_periphs_a_90_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_90_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_91_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_91_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_91_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_91_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_91_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_91_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_91_mux_set(alsaqr_periph_padframe_periphs_a_91_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_91_mux_sel_t alsaqr_periph_padframe_periphs_a_91_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_91_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_a_92_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_a_92_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_a_92_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_92_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_a_92_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_a_92_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_a_92_mux_set(alsaqr_periph_padframe_periphs_a_92_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_a_92_mux_sel_t alsaqr_periph_padframe_periphs_a_92_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_A_92_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_00_mux_sel_t alsaqr_periph_padframe_periphs_b_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_01_mux_sel_t alsaqr_periph_padframe_periphs_b_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_02_mux_sel_t alsaqr_periph_padframe_periphs_b_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_03_mux_sel_t alsaqr_periph_padframe_periphs_b_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_04_mux_sel_t alsaqr_periph_padframe_periphs_b_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_05_mux_sel_t alsaqr_periph_padframe_periphs_b_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_06_mux_sel_t alsaqr_periph_padframe_periphs_b_06_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_06_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_07_mux_sel_t alsaqr_periph_padframe_periphs_b_07_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_07_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_08_mux_sel_t alsaqr_periph_padframe_periphs_b_08_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_08_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_09_mux_sel_t alsaqr_periph_padframe_periphs_b_09_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_09_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_10_mux_sel_t alsaqr_periph_padframe_periphs_b_10_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_10_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_11_mux_sel_t alsaqr_periph_padframe_periphs_b_11_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_11_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_12_mux_sel_t alsaqr_periph_padframe_periphs_b_12_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_12_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_13_mux_sel_t alsaqr_periph_padframe_periphs_b_13_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_13_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_14_mux_sel_t alsaqr_periph_padframe_periphs_b_14_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_14_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_15_mux_sel_t alsaqr_periph_padframe_periphs_b_15_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_15_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_16_mux_sel_t alsaqr_periph_padframe_periphs_b_16_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_16_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_17_mux_sel_t alsaqr_periph_padframe_periphs_b_17_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_17_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_18_mux_sel_t alsaqr_periph_padframe_periphs_b_18_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_18_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_19_mux_sel_t alsaqr_periph_padframe_periphs_b_19_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_19_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_20_mux_sel_t alsaqr_periph_padframe_periphs_b_20_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_20_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_21_mux_sel_t alsaqr_periph_padframe_periphs_b_21_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_21_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_22_mux_sel_t alsaqr_periph_padframe_periphs_b_22_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_22_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_23_mux_sel_t alsaqr_periph_padframe_periphs_b_23_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_23_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_24_mux_sel_t alsaqr_periph_padframe_periphs_b_24_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_24_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_25_mux_sel_t alsaqr_periph_padframe_periphs_b_25_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_25_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_26_mux_sel_t alsaqr_periph_padframe_periphs_b_26_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_26_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_27_mux_sel_t alsaqr_periph_padframe_periphs_b_27_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_27_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_28_mux_sel_t alsaqr_periph_padframe_periphs_b_28_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_28_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_29_mux_sel_t alsaqr_periph_padframe_periphs_b_29_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_29_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_30_mux_sel_t alsaqr_periph_padframe_periphs_b_30_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_30_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_31_mux_sel_t alsaqr_periph_padframe_periphs_b_31_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_31_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_32_mux_sel_t alsaqr_periph_padframe_periphs_b_32_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_32_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_33_mux_sel_t alsaqr_periph_padframe_periphs_b_33_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_33_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_34_mux_sel_t alsaqr_periph_padframe_periphs_b_34_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_34_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_35_mux_sel_t alsaqr_periph_padframe_periphs_b_35_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_35_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_36_mux_sel_t alsaqr_periph_padframe_periphs_b_36_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_36_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_37_mux_sel_t alsaqr_periph_padframe_periphs_b_37_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_37_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_38_mux_sel_t alsaqr_periph_padframe_periphs_b_38_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_38_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_39_mux_sel_t alsaqr_periph_padframe_periphs_b_39_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_39_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_40_mux_sel_t alsaqr_periph_padframe_periphs_b_40_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_40_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_41_mux_sel_t alsaqr_periph_padframe_periphs_b_41_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_41_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_42_mux_sel_t alsaqr_periph_padframe_periphs_b_42_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_42_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_43_mux_sel_t alsaqr_periph_padframe_periphs_b_43_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_43_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_44_mux_sel_t alsaqr_periph_padframe_periphs_b_44_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_44_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_45_mux_sel_t alsaqr_periph_padframe_periphs_b_45_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_45_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_46_mux_sel_t alsaqr_periph_padframe_periphs_b_46_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_46_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

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

void alsaqr_periph_padframe_periphs_b_48_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_48_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_48_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_48_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_48_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_48_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_48_mux_set(alsaqr_periph_padframe_periphs_b_48_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_48_mux_sel_t alsaqr_periph_padframe_periphs_b_48_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_48_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_49_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_49_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_49_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_49_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_49_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_49_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_49_mux_set(alsaqr_periph_padframe_periphs_b_49_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_49_mux_sel_t alsaqr_periph_padframe_periphs_b_49_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_49_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_50_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_50_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_50_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_50_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_50_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_50_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_50_mux_set(alsaqr_periph_padframe_periphs_b_50_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_50_mux_sel_t alsaqr_periph_padframe_periphs_b_50_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_50_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_51_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_51_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_51_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_51_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_51_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_51_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_51_mux_set(alsaqr_periph_padframe_periphs_b_51_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_51_mux_sel_t alsaqr_periph_padframe_periphs_b_51_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_51_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_52_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_52_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_52_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_52_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_52_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_52_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_52_mux_set(alsaqr_periph_padframe_periphs_b_52_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_52_mux_sel_t alsaqr_periph_padframe_periphs_b_52_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_52_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_53_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_53_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_53_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_53_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_53_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_53_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_53_mux_set(alsaqr_periph_padframe_periphs_b_53_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_53_mux_sel_t alsaqr_periph_padframe_periphs_b_53_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_53_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_54_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_54_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_54_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_54_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_54_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_54_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_54_mux_set(alsaqr_periph_padframe_periphs_b_54_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_54_mux_sel_t alsaqr_periph_padframe_periphs_b_54_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_54_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_55_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_55_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_55_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_55_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_55_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_55_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_55_mux_set(alsaqr_periph_padframe_periphs_b_55_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_55_mux_sel_t alsaqr_periph_padframe_periphs_b_55_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_55_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_56_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_56_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_56_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_56_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_56_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_56_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_56_mux_set(alsaqr_periph_padframe_periphs_b_56_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_56_mux_sel_t alsaqr_periph_padframe_periphs_b_56_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_56_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_57_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_57_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_57_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_57_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_57_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_57_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_57_mux_set(alsaqr_periph_padframe_periphs_b_57_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_57_mux_sel_t alsaqr_periph_padframe_periphs_b_57_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_57_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_58_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_58_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_58_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_58_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_58_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_58_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_58_mux_set(alsaqr_periph_padframe_periphs_b_58_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_58_mux_sel_t alsaqr_periph_padframe_periphs_b_58_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_58_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_59_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_59_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_59_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_59_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_59_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_59_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_59_mux_set(alsaqr_periph_padframe_periphs_b_59_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_59_mux_sel_t alsaqr_periph_padframe_periphs_b_59_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_59_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_60_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_60_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_60_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_60_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_60_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_60_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_60_mux_set(alsaqr_periph_padframe_periphs_b_60_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_60_mux_sel_t alsaqr_periph_padframe_periphs_b_60_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_60_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_61_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_61_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_61_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_61_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_61_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_61_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_61_mux_set(alsaqr_periph_padframe_periphs_b_61_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_61_mux_sel_t alsaqr_periph_padframe_periphs_b_61_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_61_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_b_62_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_b_62_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_b_62_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_62_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_b_62_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_b_62_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_b_62_mux_set(alsaqr_periph_padframe_periphs_b_62_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_b_62_mux_sel_t alsaqr_periph_padframe_periphs_b_62_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_B_62_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 2;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_00_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_01_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_02_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_02_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_02_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_03_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_03_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_03_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_04_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_04_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_04_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_qspi_05_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_05_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_qspi_05_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_QSPI_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_00_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_00_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_01_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_01_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_02_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_02_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_02_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_02_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_02_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_03_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_03_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_03_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_03_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_03_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_04_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_04_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_04_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_04_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_04_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_linux_qspi_05_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_05_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_linux_qspi_05_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_05_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_LINUX_QSPI_05_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_00_mux_set(alsaqr_periph_padframe_periphs_ot_gpio_00_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_gpio_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_gpio_00_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_00_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_chip2pad_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_CHIP2PAD_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_chip2pad_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_CHIP2PAD_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_drv_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_field32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_DRV_FIELD, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_drv_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_field32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_DRV_FIELD);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_oen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_OEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_oen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_OEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_puen_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_PUEN_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_puen_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_PUEN_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_slw_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_SLW_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_slw_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_SLW_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_smt_set(uint8_t value) {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  reg = bitfield_bit32_write(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_SMT_BIT, value);
  REG_WRITE32(address, reg);
}

uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_smt_get() {
  uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_REG_OFFSET;
  uint32_t reg = REG_READ32(address);
  return bitfield_bit32_read(reg, ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_CFG_SMT_BIT);
}

void alsaqr_periph_padframe_periphs_ot_gpio_01_mux_set(alsaqr_periph_padframe_periphs_ot_gpio_01_mux_sel_t mux_sel) {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;
  uint32_t field_mask = (1<<sel_size)-1;
  REG_WRITE32(address, mux_sel & field_mask);
}

alsaqr_periph_padframe_periphs_ot_gpio_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_gpio_01_mux_get() {
  const uint32_t address = ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS + ALSAQR_PERIPH_PADFRAME_PERIPHS_CONFIG_OT_GPIO_01_MUX_SEL_REG_OFFSET;
  const uint32_t sel_size = 1;

  uint32_t field_mask = (1<<sel_size)-1;
  return REG_READ32(address) & field_mask;
}
