// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i3c.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

/**
 * HCI Queues are mapped as a single memory window.
 */
#define I3C_COMMAND_QUEUE_REG_OFFSET I3C_HCI_PORTS_REG_OFFSET
#define I3C_RESPONSE_QUEUE_REG_OFFSET I3C_HCI_PORTS_REG_OFFSET + 4u
#define I3C_XFER_DATA_PORT_REG_OFFSET I3C_HCI_PORTS_REG_OFFSET + 8u
#define I3C_IBI_PORT_REG_OFFSET I3C_HCI_PORTS_REG_OFFSET + 12u

/**
 * TTI Queues are mapped as a single memory window.
 */
#define I3C_TARGET_RXD_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET
#define I3C_TARGET_RX_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 4u
#define I3C_TARGET_IBID_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 8u
#define I3C_TARGET_IBI_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 12u
#define I3C_TARGET_ASYNC_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 16u
#define I3C_TARGET0_TXD_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 20u
#define I3C_TARGET1_TXD_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 24u
#define I3C_TARGET2_TXD_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 28u
#define I3C_TARGET3_TXD_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 32u
#define I3C_TARGET0_TX_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 36u
#define I3C_TARGET1_TX_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 40u
#define I3C_TARGET2_TX_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 44u
#define I3C_TARGET3_TX_REG_OFFSET I3C_TTI_PORTS_REG_OFFSET + 48u

// Interrupt-group related registers.
#define I3C_INTR_REG_OFFSETS(x)                                             \
  {I3C_##x##INTR_STATUS_REG_OFFSET, I3C_##x##INTR_STATUS_ENABLE_REG_OFFSET, \
   I3C_##x##INTR_SIGNAL_ENABLE_REG_OFFSET, I3C_##x##INTR_FORCE_REG_OFFSET}

static const struct {
  uint32_t status;
  uint32_t status_en;
  uint32_t signal_en;
  uint32_t force;
} intr_regs[] = {
    // kDifI3CIntrGroup_HCI registers offsets.
    I3C_INTR_REG_OFFSETS(),
    // kDifI3CIntrGroup_PIO registers offsets.
    I3C_INTR_REG_OFFSETS(PIO_),
    // kDifI3CIntrGroup_StbyCr registers offsets.
    {I3C_STBY_CR_INTR_STATUS_REG_OFFSET,
     ~0u,  // No STATUS_ENABLE register for this group.
     I3C_STBY_CR_INTR_SIGNAL_ENABLE_REG_OFFSET,
     I3C_STBY_CR_INTR_FORCE_REG_OFFSET},
    // kDifI3CIntrGroup_Targ registers offsets.
    I3C_INTR_REG_OFFSETS(TARG_)};

// Faster DWORD-copying routines for use with the I3C queues.
static dif_result_t dif_i3c_queue_raw_write(const dif_i3c_t *i3c,
                                            dif_i3c_queue_t id,
                                            const uint8_t *src,
                                            uint16_t src_len);
static dif_result_t dif_i3c_queue_raw_read(const dif_i3c_t *i3c,
                                           dif_i3c_queue_t id, uint8_t *dst,
                                           uint16_t dst_len);

// Dummy `SIZE_VAL` field access for use with the TTI queues/buffers.
#define I3C_NO_SIZE_VAL_FIELD ((bitfield_field32_t){.mask = 0u, .index = 0})

// The TTI queues/buffers do not have `SIZE_VAL` fields.
#define I3C_IBI_STAT_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXBUF_CONFIG_0_SIZE_VAL_0_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXBUF_CONFIG_1_SIZE_VAL_1_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXBUF_CONFIG_2_SIZE_VAL_2_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXBUF_CONFIG_3_SIZE_VAL_3_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXDESC_CONFIG_0_SIZE_VAL_0_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXDESC_CONFIG_1_SIZE_VAL_1_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXDESC_CONFIG_2_SIZE_VAL_2_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_TXDESC_CONFIG_3_SIZE_VAL_3_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_RXBUF_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_RXDESC_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_IBI_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_IBIDESC_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD
#define I3C_TARG_ASYNC_CONFIG_SIZE_VAL_FIELD I3C_NO_SIZE_VAL_FIELD

// Configuration of a physical queue.
#define I3C_PHYSQ_CONFIG(x, y)                \
  {I3C_##x##_CONFIG##y##_REG_OFFSET,          \
   I3C_##x##_CONFIG##y##_MIN_ADDR##y##_FIELD, \
   I3C_##x##_CONFIG##y##_MAX_ADDR##y##_FIELD, \
   I3C_##x##_CONFIG##y##_SIZE_VAL##y##_FIELD}

// Indexed by the `dif_i3c_phys_queue_t` queue identifier.
static const struct {
  ptrdiff_t offset;
  bitfield_field32_t min_addr;
  bitfield_field32_t max_addr;
  bitfield_field32_t size_val;
} physq_config[] = {
    // HCI queues/buffers.
    I3C_PHYSQ_CONFIG(CTRL_TXBUF, ), I3C_PHYSQ_CONFIG(CTRL_RXBUF, ),
    I3C_PHYSQ_CONFIG(COMMAND_QUEUE, ), I3C_PHYSQ_CONFIG(RESPONSE_QUEUE, ),
    I3C_PHYSQ_CONFIG(IBI, ), I3C_PHYSQ_CONFIG(IBI_STAT, ),

    // TTI queues/buffers.
    I3C_PHYSQ_CONFIG(TARG_TXBUF, _0), I3C_PHYSQ_CONFIG(TARG_TXBUF, _1),
    I3C_PHYSQ_CONFIG(TARG_TXBUF, _2), I3C_PHYSQ_CONFIG(TARG_TXBUF, _3),
    I3C_PHYSQ_CONFIG(TARG_TXDESC, _0), I3C_PHYSQ_CONFIG(TARG_TXDESC, _1),
    I3C_PHYSQ_CONFIG(TARG_TXDESC, _2), I3C_PHYSQ_CONFIG(TARG_TXDESC, _3),
    I3C_PHYSQ_CONFIG(TARG_RXBUF, ), I3C_PHYSQ_CONFIG(TARG_RXDESC, ),
    I3C_PHYSQ_CONFIG(TARG_IBI, ), I3C_PHYSQ_CONFIG(TARG_IBIDESC, ),
    I3C_PHYSQ_CONFIG(TARG_ASYNC, )};

/**
 * Mapping from queue ID to register offset.
 */
static ptrdiff_t get_queue_offset(dif_i3c_queue_t id) {
  switch (id) {
    // HCI Queues.
    case kDifI3CQueueCommand:
      return I3C_COMMAND_QUEUE_REG_OFFSET;
    case kDifI3CQueueResponse:
      return I3C_RESPONSE_QUEUE_REG_OFFSET;
    case kDifI3CQueueXfer:
      return I3C_XFER_DATA_PORT_REG_OFFSET;
    case kDifI3CQueueIBI:
      return I3C_IBI_PORT_REG_OFFSET;

    // TTI Queues.
    case kDifI3CQueueTxData0:
      return I3C_TARGET0_TX_REG_OFFSET;
    case kDifI3CQueueTxData1:
      return I3C_TARGET1_TX_REG_OFFSET;
    case kDifI3CQueueTxData2:
      return I3C_TARGET2_TX_REG_OFFSET;
    case kDifI3CQueueTxData3:
      return I3C_TARGET3_TX_REG_OFFSET;
    case kDifI3CQueueTxDesc0:
      return I3C_TARGET0_TXD_REG_OFFSET;
    case kDifI3CQueueTxDesc1:
      return I3C_TARGET1_TXD_REG_OFFSET;
    case kDifI3CQueueTxDesc2:
      return I3C_TARGET2_TXD_REG_OFFSET;
    case kDifI3CQueueTxDesc3:
      return I3C_TARGET3_TXD_REG_OFFSET;
    case kDifI3CQueueRxData:
      return I3C_TARGET_RX_REG_OFFSET;
    case kDifI3CQueueRxDesc:
      return I3C_TARGET_RXD_REG_OFFSET;
    case kDifI3CQueueIBIData:
      return I3C_TARGET_IBI_REG_OFFSET;
    case kDifI3CQueueIBIDesc:
      return I3C_TARGET_IBID_REG_OFFSET;
    case kDifI3CQueueAsyncEvt:
      return I3C_TARGET_ASYNC_REG_OFFSET;
    default:
      return -1;
  }
}

// Return the current message buffer allocation of the given queue.
dif_result_t dif_i3c_config_queue_get(const dif_i3c_t *i3c,
                                      dif_i3c_phys_queue_t id,
                                      unsigned *min_addr, unsigned *max_addr,
                                      unsigned *size_val) {
  if (i3c == NULL ||
      (id >=
       sizeof(physq_config) /
           sizeof(physq_config[0]))) {  // TODO: Is there a macro somewhere?
    return kDifBadArg;
  }

  uint32_t config = mmio_region_read32(i3c->base_addr, physq_config[id].offset);
  if (min_addr)
    *min_addr = bitfield_field32_read(config, physq_config[id].min_addr);
  if (max_addr)
    *max_addr = bitfield_field32_read(config, physq_config[id].max_addr);
  if (size_val)
    *size_val = bitfield_field32_read(config, physq_config[id].size_val);

  return kDifOk;
}

// Configure the message buffer allocation of the given queue.
// Note: This is a low-level API and the caller is trusted to ensure that
// queues do not overlap.
// TODO: Currently the size value is trusted completely; we could check it for
// consistency with the supplied range, remembering that these are HCI-only.
dif_result_t dif_i3c_config_queue_set(const dif_i3c_t *i3c,
                                      dif_i3c_phys_queue_t id,
                                      unsigned min_addr, unsigned max_addr,
                                      unsigned size_val) {
  if (i3c == NULL || (id >= sizeof(physq_config) / sizeof(physq_config[0]))) {
    return kDifBadArg;
  }

  uint32_t config = mmio_region_read32(i3c->base_addr, physq_config[id].offset);
  config = bitfield_field32_write(config, physq_config[id].min_addr, min_addr);
  config = bitfield_field32_write(config, physq_config[id].max_addr, max_addr);
  config = bitfield_field32_write(config, physq_config[id].size_val, size_val);
  mmio_region_write32(i3c->base_addr, physq_config[id].offset, config);

  return kDifOk;
}

// Supply Controller configuration.
dif_result_t dif_i3c_ctrl_configure(const dif_i3c_t *i3c,
                                    const dif_i3c_ctrl_config_t *cfg) {
  if (i3c == NULL) {
    return kDifBadArg;
  }

  uint32_t pio_control =
      bitfield_bit32_write(0U, I3C_PIO_CONTROL_ENABLE_BIT, 1u);
  pio_control = bitfield_bit32_write(pio_control, I3C_PIO_CONTROL_RS_BIT, 1u);
  mmio_region_write32(i3c->base_addr, I3C_PIO_CONTROL_REG_OFFSET, pio_control);

  return kDifOk;
}

// Configure a Virtual Target.
dif_result_t dif_i3c_targ_configure(const dif_i3c_t *i3c, unsigned idx,
                                    const dif_i3c_targ_config_t *cfg) {
  if (i3c == NULL) {
    return kDifBadArg;
  }

  uint32_t addr = mmio_region_read32(
      i3c->base_addr, I3C_TARG_ADDR_0_REG_OFFSET + (ptrdiff_t)(idx * 4u));
  addr = bitfield_field32_write(addr, I3C_TARG_ADDR_0_STATIC_ADDR_0_FIELD,
                                cfg->static_addr);
  addr = bitfield_bit32_write(addr, I3C_TARG_ADDR_0_STATIC_ADDR_VALID_0_BIT,
                              cfg->static_addr_valid ? 1u : 0u);

  // TODO: This should not be done, but we presently do not have DAA working.
  addr = bitfield_field32_write(addr, I3C_TARG_ADDR_0_DYNAMIC_ADDR_0_FIELD,
                                cfg->static_addr);
  addr = bitfield_bit32_write(addr, I3C_TARG_ADDR_0_DYNAMIC_ADDR_VALID_0_BIT,
                              cfg->static_addr_valid ? 1u : 0u);

  mmio_region_write32(i3c->base_addr,
                      I3C_TARG_ADDR_0_REG_OFFSET + (ptrdiff_t)(idx * 4u), addr);

  // TODO: Other configuration - max read/write, mwl, mrl, ibi.
  //  mmio_region_write32(i3c->base_addr, I3C_TARG_);
  //  mmio_region_write32(i3c->base_addr, I3C_TARG_);

  return kDifOk;
}

// Return the current global state of the I3C Target peripheral.
dif_result_t dif_i3c_targ_state(const dif_i3c_t *i3c,
                                dif_i3c_targ_state_t *state) {
  if (i3c == NULL || state == NULL) {
    return kDifBadArg;
  }

  // TODO: Read TARG_STATUS register and return.
  //  mmio_region_read32(i3c->base_addr, I3C_TARG_STATUS_OFFSET);
  //  if (bitfield_bit32_read(

  return kDifOk;
}

// Set the operation mode of the Controller.
dif_result_t dif_i3c_ctrl_mode_set(const dif_i3c_t *i3c,
                                   dif_i3c_ctrl_mode_t mode) {
  if (i3c == NULL) {
    return kDifBadArg;
  }

  switch (mode) {
    case kI3CCtrlMode_Disabled:
      mmio_region_write32(i3c->base_addr, I3C_STBY_CR_CONTROL_REG_OFFSET,
                          0u << 30);
      mmio_region_write32(i3c->base_addr, I3C_HC_CONTROL_REG_OFFSET, 0u);
      break;
    case kI3CCtrlMode_Active:
      mmio_region_write32(i3c->base_addr, I3C_STBY_CR_CONTROL_REG_OFFSET,
                          1u << 30);
      mmio_region_write32(i3c->base_addr, I3C_HC_CONTROL_REG_OFFSET, 1u << 31);
      break;
    case kI3CCtrlMode_Standby:
      mmio_region_write32(i3c->base_addr, I3C_STBY_CR_CONTROL_REG_OFFSET,
                          2u << 30);
      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

// Specify which of the Virtual Targets are enabled.
dif_result_t dif_i3c_targ_enables_set(const dif_i3c_t *i3c, uint32_t enables) {
  if (i3c == NULL) {
    return kDifBadArg;
  }

  uint32_t control =
      mmio_region_read32(i3c->base_addr, I3C_TARG_CONTROL_REG_OFFSET);
  control =
      bitfield_bit32_write(control, I3C_TARG_CONTROL_EN_BIT, enables ? 1u : 0u);
  mmio_region_write32(i3c->base_addr, I3C_TARG_CONTROL_REG_OFFSET, control);

  mmio_region_write32(i3c->base_addr, I3C_TARG_ENABLE_REG_OFFSET, enables);

  return kDifOk;
}

// Write to an entry within the DAT, describing a Target/Group.
dif_result_t dif_i3c_dat_entry_set(const dif_i3c_t *i3c, uint8_t idx,
                                   const dif_i3c_dat_entry_t *entry) {
  if (i3c == NULL || idx >= I3C_NUM_DAT_ENTRIES) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset =
      (ptrdiff_t)(I3C_DAT_REG_OFFSET + (idx * sizeof(*entry)));
  const uint32_t *sptr = (uint32_t *)entry;
  for (unsigned i = 0u; i < sizeof(*entry) / 4; i++) {
    mmio_region_write32(i3c->base_addr, reg_offset, sptr[i]);
    reg_offset += 4;
  }
  return kDifOk;
}

// Read the current index of the DCT.
dif_result_t dif_i3c_dct_index_get(const dif_i3c_t *i3c, uint8_t *idx) {
  if (i3c == NULL) {
    return kDifBadArg;
  }
  uint32_t offset =
      mmio_region_read32(i3c->base_addr, I3C_DCT_SECTION_OFFSET_REG_OFFSET);
  *idx = (uint8_t)bitfield_field32_read(
      offset, I3C_DCT_SECTION_OFFSET_TABLE_INDEX_FIELD);
  return kDifOk;
}

// Set the current index of the DCT.
dif_result_t dif_i3c_dct_index_set(const dif_i3c_t *i3c, uint8_t idx) {
  if (i3c == NULL || idx >= I3C_NUM_DCT_ENTRIES) {
    return kDifBadArg;
  }
  // The other fields within this register are Read Only.
  uint32_t offset =
      bitfield_field32_write(0u, I3C_DCT_SECTION_OFFSET_TABLE_INDEX_FIELD, idx);
  mmio_region_write32(i3c->base_addr, I3C_DCT_SECTION_OFFSET_REG_OFFSET,
                      offset);
  return kDifOk;
}

// Read an entry from within the DCT, describing a Target.
dif_result_t dif_i3c_dct_entry_get(const dif_i3c_t *i3c, uint8_t idx,
                                   dif_i3c_dct_entry_t *entry) {
  if (i3c == NULL || idx >= I3C_NUM_DCT_ENTRIES) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset =
      (ptrdiff_t)(I3C_DCT_REG_OFFSET + (idx * sizeof(*entry)));
  uint32_t *dptr = (uint32_t *)entry;
  for (unsigned i = 0u; i < sizeof(*entry) / 4; i++) {
    dptr[i] = mmio_region_read32(i3c->base_addr, reg_offset);
    reg_offset += 4;
  }
  return kDifOk;
}

// Write data to the XFER_DATA_PORT of the HCI.
dif_result_t dif_i3c_xfer_write(const dif_i3c_t *i3c, const uint32_t *data,
                                uint16_t nbytes) {
  if (i3c == NULL || data == NULL || nbytes >= I3C_BUFFER_BYTES) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueXfer, (uint8_t *)data,
                                 nbytes);
}

// Queue a Command Descriptor.
dif_result_t dif_i3c_command_write(const dif_i3c_t *i3c,
                                   const dif_i3c_cmd_desc_t *cmd, uint8_t num) {
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueCommand, (uint8_t *)cmd,
                                 num * sizeof(*cmd));
}

// Retrieve a Response Descriptor.
dif_result_t dif_i3c_response_read(const dif_i3c_t *i3c,
                                   dif_i3c_rsp_desc_t *rsp, uint8_t num) {
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueResponse, (uint8_t *)rsp,
                                num * sizeof(*rsp));
}

// Read data from the XFER_DATA_PORT of the HCI.
dif_result_t dif_i3c_xfer_read(const dif_i3c_t *i3c, uint32_t *buf,
                               uint16_t nbytes) {
  if (i3c == NULL || buf == NULL || nbytes >= I3C_BUFFER_BYTES) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueXfer, (uint8_t *)buf, nbytes);
}

// Return information on the Controller queues.
dif_result_t dif_i3c_queue_levels_read(const dif_i3c_t *i3c,
                                       dif_i3c_hci_queue_levels_t *levels) {
  if (i3c == NULL || levels == NULL) {
    return kDifBadArg;
  }

  uint32_t queue_lvl =
      mmio_region_read32(i3c->base_addr, I3C_QUEUE_STATUS_LEVEL_REG_OFFSET);
  levels->cmd_queue_free = (uint8_t)bitfield_field32_read(
      queue_lvl, I3C_QUEUE_STATUS_LEVEL_CMD_QUEUE_FREE_LVL_FIELD);
  levels->rsp_buffer_level = (uint8_t)bitfield_field32_read(
      queue_lvl, I3C_QUEUE_STATUS_LEVEL_RESPONSE_BUFFER_LVL_FIELD);
  levels->ibi_buffer_level = (uint8_t)bitfield_field32_read(
      queue_lvl, I3C_QUEUE_STATUS_LEVEL_IBI_BUFFER_LVL_FIELD);
  levels->ibi_status_cnt = (uint8_t)bitfield_field32_read(
      queue_lvl, I3C_QUEUE_STATUS_LEVEL_IBI_STATUS_CNT_FIELD);

  return kDifOk;
}

// Return information on the Tx and Rx Buffers of the HCI.
dif_result_t dif_i3c_buffer_levels_read(const dif_i3c_t *i3c,
                                        dif_i3c_hci_buffer_levels_t *levels) {
  if (i3c == NULL || levels == NULL) {
    return kDifBadArg;
  }

  uint32_t buffer_lvl = mmio_region_read32(
      i3c->base_addr, I3C_DATA_BUFFER_STATUS_LEVEL_REG_OFFSET);
  levels->rx_buffer_level = (uint8_t)bitfield_field32_read(
      buffer_lvl, I3C_DATA_BUFFER_STATUS_LEVEL_RX_BUF_LVL_FIELD);
  levels->tx_buffer_free = (uint8_t)bitfield_field32_read(
      buffer_lvl, I3C_DATA_BUFFER_STATUS_LEVEL_TX_BUF_FREE_LVL_FIELD);

  return kDifOk;
}

// Return information on the Target-side queues.
dif_result_t dif_i3c_targ_queue_levels_read(
    const dif_i3c_t *i3c, dif_i3c_tti_queue_levels_t *levels) {
  if (i3c == NULL || levels == NULL) {
    return kDifBadArg;
  }

  uint32_t vals = mmio_region_read32(i3c->base_addr,
                                     I3C_TARG_QUEUE_STATUS_LEVEL_REG_OFFSET);
  levels->async_level = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_QUEUE_STATUS_LEVEL_ASYNC_EVT_LVL_FIELD);
  levels->rx_desc_level = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_QUEUE_STATUS_LEVEL_RX_DESC_LVL_FIELD);
  return kDifOk;
}

// Return information on the Target-side data buffers.
dif_result_t dif_i3c_targ_buf_levels_read(const dif_i3c_t *i3c,
                                          dif_i3c_tti_buf_levels_t *levels) {
  if (i3c == NULL || levels == NULL) {
    return kDifBadArg;
  }

  uint32_t vals =
      mmio_region_read32(i3c->base_addr, I3C_TARG_BUF_STATUS_LEVEL_REG_OFFSET);
  levels->ibi_free = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_BUF_STATUS_LEVEL_IBI_FREE_LVL_FIELD);
  levels->rx_buf_level = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_BUF_STATUS_LEVEL_RX_BUF_LVL_FIELD);
  return kDifOk;
}

// Return information on the Target-side (TTI) Tx queues.
dif_result_t dif_i3c_targ_tx_levels_read(const dif_i3c_t *i3c, unsigned id,
                                         dif_i3c_tti_tx_levels_t *levels) {
  if (i3c == NULL || levels == NULL || id >= I3C_NUM_VIRT_TARGETS) {
    return kDifBadArg;
  }

  uint32_t vals = mmio_region_read32(
      i3c->base_addr,
      I3C_TARG_TX_QUEUE_STATUS_LEVEL_0_REG_OFFSET + (ptrdiff_t)(id * 4u));
  levels->tx_desc_free = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_TX_QUEUE_STATUS_LEVEL_0_TX_DESC_FREE_LVL_0_FIELD);
  levels->tx_buf_free = (uint8_t)bitfield_field32_read(
      vals, I3C_TARG_TX_QUEUE_STATUS_LEVEL_0_TX_BUF_FREE_LVL_0_FIELD);
  return kDifOk;
}

// Set Controller queue thresholds.
dif_result_t dif_i3c_queue_thld_set(const dif_i3c_t *i3c,
                                    const dif_i3c_queue_thlds_t *thlds) {
  if (i3c == NULL || thlds == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl =
      bitfield_field32_write(0u, I3C_QUEUE_THLD_CTRL_CMD_EMPTY_BUF_THLD_FIELD,
                             thlds->cmd_empty_buf_thld);
  ctrl = bitfield_field32_write(ctrl, I3C_QUEUE_THLD_CTRL_RESP_BUF_THLD_FIELD,
                                thlds->resp_buf_thld);
  ctrl = bitfield_field32_write(ctrl,
                                I3C_QUEUE_THLD_CTRL_IBI_DATA_SEGMENT_SIZE_FIELD,
                                thlds->ibi_seg_size);
  ctrl = bitfield_field32_write(ctrl, I3C_QUEUE_THLD_CTRL_IBI_STATUS_THLD_FIELD,
                                thlds->ibi_status_thld);
  mmio_region_write32(i3c->base_addr, I3C_QUEUE_THLD_CTRL_REG_OFFSET, ctrl);
  return kDifOk;
}

// Get Controller queue thresholds.
dif_result_t dif_i3c_queue_thld_get(const dif_i3c_t *i3c,
                                    dif_i3c_queue_thlds_t *thlds) {
  if (i3c == NULL || thlds == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl =
      mmio_region_read32(i3c->base_addr, I3C_QUEUE_THLD_CTRL_REG_OFFSET);
  thlds->cmd_empty_buf_thld = (uint8_t)bitfield_field32_read(
      ctrl, I3C_QUEUE_THLD_CTRL_CMD_EMPTY_BUF_THLD_FIELD);
  thlds->resp_buf_thld = (uint8_t)bitfield_field32_read(
      ctrl, I3C_QUEUE_THLD_CTRL_RESP_BUF_THLD_FIELD);
  thlds->ibi_seg_size = (uint8_t)bitfield_field32_read(
      ctrl, I3C_QUEUE_THLD_CTRL_IBI_DATA_SEGMENT_SIZE_FIELD);
  thlds->ibi_status_thld = (uint8_t)bitfield_field32_read(
      ctrl, I3C_QUEUE_THLD_CTRL_IBI_STATUS_THLD_FIELD);
  return kDifOk;
}

// Set Controller buffer thresholds.
dif_result_t dif_i3c_buffer_thld_set(const dif_i3c_t *i3c,
                                     const dif_i3c_buffer_thlds_t *thlds) {
  if (i3c == NULL || thlds == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl = bitfield_field32_write(
      0u, I3C_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_FIELD, thlds->tx_buf_thld);
  ctrl = bitfield_field32_write(
      ctrl, I3C_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_FIELD, thlds->rx_buf_thld);
  ctrl = bitfield_field32_write(
      ctrl, I3C_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_FIELD, thlds->tx_start_thld);
  ctrl = bitfield_field32_write(
      ctrl, I3C_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_FIELD, thlds->rx_start_thld);
  mmio_region_write32(i3c->base_addr, I3C_DATA_BUFFER_THLD_CTRL_REG_OFFSET,
                      ctrl);
  return kDifOk;
}

// Get Controller buffer thresholds.
dif_result_t dif_i3c_buffer_thld_get(const dif_i3c_t *i3c,
                                     dif_i3c_buffer_thlds_t *thlds) {
  if (i3c == NULL || thlds == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl =
      mmio_region_read32(i3c->base_addr, I3C_DATA_BUFFER_THLD_CTRL_REG_OFFSET);
  thlds->tx_buf_thld =
      bitfield_field32_read(ctrl, I3C_DATA_BUFFER_THLD_CTRL_TX_BUF_THLD_FIELD);
  thlds->rx_buf_thld =
      bitfield_field32_read(ctrl, I3C_DATA_BUFFER_THLD_CTRL_RX_BUF_THLD_FIELD);
  thlds->tx_start_thld = bitfield_field32_read(
      ctrl, I3C_DATA_BUFFER_THLD_CTRL_TX_START_THLD_FIELD);
  thlds->rx_start_thld = bitfield_field32_read(
      ctrl, I3C_DATA_BUFFER_THLD_CTRL_RX_START_THLD_FIELD);
  return kDifOk;
}

dif_result_t dif_i3c_ctrl_desc_ibi_recv(const dif_i3c_t *i3c,
                                        dif_i3c_ibi_stat_desc_t *desc) {
  if (i3c == NULL || desc == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueIBIDesc, (uint8_t *)desc,
                                sizeof(*desc));
}

dif_result_t dif_i3c_ctrl_data_ibi_recv(const dif_i3c_t *i3c, uint32_t *buf,
                                        uint16_t nbytes) {
  if (i3c == NULL || buf == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueIBIData, (uint8_t *)buf,
                                nbytes);
}

dif_result_t dif_i3c_targ_send(const dif_i3c_t *i3c, unsigned id,
                               const dif_i3c_tti_tx_desc_t *desc,
                               const uint32_t *data, uint16_t nbytes) {
  if (i3c == NULL || desc == NULL || id >= I3C_NUM_VIRT_TARGETS) {
    return kDifBadArg;
  }
  if (data) {
    dif_result_t res = dif_i3c_queue_raw_write(i3c, kDifI3CQueueTxData0 + id,
                                               (uint8_t *)data, nbytes);
    if (res != kDifOk) {
      return res;
    }
  }
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueTxDesc0 + id, (uint8_t *)desc,
                                 sizeof(*desc));
}

dif_result_t dif_i3c_targ_data_send(const dif_i3c_t *i3c, unsigned id,
                                    const uint32_t *data, uint16_t nbytes) {
  if (i3c == NULL || data == NULL || id >= I3C_NUM_VIRT_TARGETS) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueTxData0 + id, (uint8_t *)data,
                                 nbytes);
}

dif_result_t dif_i3c_targ_recv(const dif_i3c_t *i3c,
                               dif_i3c_tti_rx_desc_t *desc, unsigned num) {
  if (i3c == NULL || desc == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueRxDesc, (uint8_t *)desc,
                                (uint16_t)(num * sizeof(*desc)));
}

dif_result_t dif_i3c_targ_data_recv(const dif_i3c_t *i3c, uint32_t *buf,
                                    uint16_t nbytes) {
  if (i3c == NULL || buf == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueRxData, (uint8_t *)buf,
                                nbytes);
}

dif_result_t dif_i3c_targ_desc_ibi_send(const dif_i3c_t *i3c,
                                        const dif_i3c_tti_ibi_status_t *desc,
                                        const uint32_t *data, uint16_t nbytes) {
  if (desc == NULL || data == NULL) {
    return kDifBadArg;
  }
  if (data) {
    dif_result_t res = dif_i3c_queue_raw_write(i3c, kDifI3CQueueIBIData,
                                               (uint8_t *)data, nbytes);
    if (res != kDifOk) {
      return res;
    }
  }
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueIBIDesc, (uint8_t *)desc,
                                 sizeof(*desc));
}

dif_result_t dif_i3c_targ_data_ibi_send(const dif_i3c_t *i3c,
                                        const uint8_t *data, uint16_t nbytes) {
  if (i3c == NULL || data == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_write(i3c, kDifI3CQueueIBIData, (uint8_t *)data,
                                 nbytes);
}

dif_result_t dif_i3c_async_evt_recv(const dif_i3c_t *i3c,
                                    dif_i3c_tti_async_evt_t *descs,
                                    uint8_t num) {
  if (i3c == NULL || descs == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, kDifI3CQueueAsyncEvt, (uint8_t *)descs,
                                num * sizeof(*descs));
}

// Push a number of 32-bit DWORDs into the specified queue of the I3C IP block.
dif_result_t dif_i3c_queue_push(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                const uint32_t data[], uint16_t n) {
  if (i3c == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_write(i3c, id, (uint8_t *)data, (uint16_t)(n << 2));
}

// Push a number of 32-bit DWORDs supplied by a callback function into the
// specified queue of the I3C IP block.
dif_result_t dif_i3c_queue_push_cb(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                   dif_i3c_tx_cb_t cb, void *ws, uint16_t n) {
  if (i3c == NULL || cb == NULL) {
    return kDifBadArg;
  }

  const ptrdiff_t queue_offset = get_queue_offset(id);
  if (queue_offset < 0) {
    return kDifBadArg;
  }

  // Transfer each DWORD from the callback function to the queue.
  dif_result_t res = kDifOk;
  unsigned idx = 0u;
  while (idx < n) {
    uint32_t d;
    res = cb(ws, &d);
    if (res != kDifOk) {
      break;
    }
    mmio_region_write32(i3c->base_addr, queue_offset, d);
    ++idx;
  }

  return res;
}

// Pop a number of 32-bit DWORDs from the specified queue of the I3C IP block.
dif_result_t dif_i3c_queue_pop(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                               uint32_t *buf, uint16_t n) {
  if (i3c == NULL || buf == NULL) {
    return kDifBadArg;
  }
  return dif_i3c_queue_raw_read(i3c, id, (uint8_t *)buf, (uint16_t)(n << 2));
}

// Pop a number of 32-bit DWORDs from the specified queue of the I3C IP block,
// passing each DWORD to a callback function.
dif_result_t dif_i3c_queue_pop_cb(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                  dif_i3c_rx_cb_t cb, void *ws, uint16_t n) {
  if (i3c == NULL || cb == NULL) {
    return kDifBadArg;
  }
  const ptrdiff_t queue_offset = get_queue_offset(id);
  if (queue_offset < 0) {
    return kDifBadArg;
  }

  // Shuffle each DWORD from the queue to the callback function.
  dif_result_t res = kDifOk;
  unsigned idx = 0u;
  while (res == kDifOk && idx < n) {
    res = cb(ws, mmio_region_read32(i3c->base_addr, queue_offset));
    ++idx;
  }

  return res;
}

// Raw data write to a queue/buffer.
dif_result_t dif_i3c_queue_raw_write(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                     const uint8_t *src, uint16_t src_len) {
  if (i3c == NULL || src == NULL || misalignment32_of((uintptr_t)src)) {
    return kDifBadArg;
  }

  const ptrdiff_t queue_offset = get_queue_offset(id);
  if (queue_offset < 0) {
    return kDifBadArg;
  }

  const uint32_t *restrict ews = (uint32_t *)(src + (src_len & ~15u));
  const uint32_t *restrict ws = (uint32_t *)src;

  // Transfer blocks of 4 x 32-bit words at a time; use the mmio_ routines for
  // compliance and to operate correctly with the DIF mocks, although this
  // results in transfers taking 50% longer because of the additional addressing
  // arithmetic and increased loop overheads.
  while (ws < ews) {
    mmio_region_write32(i3c->base_addr, queue_offset, ws[0]);
    mmio_region_write32(i3c->base_addr, queue_offset, ws[1]);
    mmio_region_write32(i3c->base_addr, queue_offset, ws[2]);
    mmio_region_write32(i3c->base_addr, queue_offset, ws[3]);
    ws += 4;
  }
  src_len &= 15u;

  if (src_len) {
    // Remaining whole words
    ews = ws + (src_len >> 2);
    while (ws < ews) {
      mmio_region_write32(i3c->base_addr, queue_offset, *ws++);
    }
    src_len &= 3u;
    if (src_len) {
      // Remaining individual bytes
      const uint8_t *restrict bs = (uint8_t *)ws;
      uint32_t d = bs[0];
      if (src_len > 1) {
        d |= ((uint32_t)bs[1] << 8);
        if (src_len > 2) {
          d |= ((uint32_t)bs[2] << 16);
        }
      }
      // Note: we can only perform full 32-bit writes to the message buffer but
      // any additional byte(s) will be ignored. Attempting byte-level writes
      // would raise exceptions.
      mmio_region_write32(i3c->base_addr, queue_offset, d);
    }
  }

  return kDifOk;
}

// Raw data read from a queue/buffer.
dif_result_t dif_i3c_queue_raw_read(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                    uint8_t *dst, uint16_t dst_len) {
  if (i3c == NULL || dst == NULL || misalignment32_of((uintptr_t)dst)) {
    return kDifBadArg;
  }

  const ptrdiff_t queue_offset = get_queue_offset(id);
  if (queue_offset < 0) {
    return kDifBadArg;
  }

  const uint32_t *restrict ewd = (uint32_t *)(dst + (dst_len & ~15u));
  uint32_t *restrict wd = (uint32_t *)dst;

  // Transfer blocks of 4 x 32-bit words at a time; use the mmio_ routines for
  // compliance and to operate correctly with the DIF mocks, although this
  // results in transfers taking 50% longer because of the additional addressing
  // arithmetic and increased loop overheads.
  while (wd < ewd) {
    wd[0] = mmio_region_read32(i3c->base_addr, queue_offset);
    wd[1] = mmio_region_read32(i3c->base_addr, queue_offset);
    wd[2] = mmio_region_read32(i3c->base_addr, queue_offset);
    wd[3] = mmio_region_read32(i3c->base_addr, queue_offset);
    wd += 4;
  }
  dst_len &= 15u;

  if (dst_len) {
    // Remaining whole words
    ewd = wd + (dst_len >> 2);
    while (wd < ewd) {
      *wd++ = mmio_region_read32(i3c->base_addr, queue_offset);
    }
    dst_len &= 3u;
    if (dst_len) {
      // Remaining individual bytes
      // Note: we can only perform full 32-bit reads from the message buffer.
      uint8_t *restrict bd = (uint8_t *)wd;
      uint32_t d = mmio_region_read32(i3c->base_addr, queue_offset);
      bd[0] = (uint8_t)d;
      if (dst_len > 1) {
        bd[1] = (uint8_t)(d >> 8);
        if (dst_len > 2) {
          bd[2] = (uint8_t)(d >> 16);
        }
      }
    }
  }

  return kDifOk;
}

// Check whether a group specifier is valid; note that the choice of enumerated
// type is implementation-defined, so to check for a value that is too low we
// cast to an integer.
static bool group_invalid(dif_i3c_intr_group_t grp) {
  return ((int)grp < 0) || (grp > kDifI3CIntrGroup_Targ);
}

// Return the current status of the interrupts within a group.
dif_result_t dif_i3c_intr_status_get(const dif_i3c_t *i3c,
                                     dif_i3c_interrupts_t *status) {
  if (status == NULL || group_invalid(status->group)) {
    return kDifBadArg;
  }
  status->interrupts = mmio_region_read32(
      i3c->base_addr, (ptrdiff_t)intr_regs[status->group].status);
  return kDifOk;
}

// Clear a set of interrupts within a group.
dif_result_t dif_i3c_intr_status_clear(const dif_i3c_t *i3c,
                                       const dif_i3c_interrupts_t *clear) {
  if (clear == NULL || group_invalid(clear->group)) {
    return kDifBadArg;
  }
  mmio_region_write32(i3c->base_addr, (ptrdiff_t)intr_regs[clear->group].status,
                      clear->interrupts);
  return kDifOk;
}

// Return the current status enables of the interrupts within a group.
dif_result_t dif_i3c_intr_status_enable_get(const dif_i3c_t *i3c,
                                            dif_i3c_interrupts_t *enables) {
  // There is no STATUS_ENABLE register for the Standby Controller Interrupt
  // group.
  if (enables == NULL || group_invalid(enables->group) ||
      intr_regs[enables->group].status_en == ~0u) {
    return kDifBadArg;
  }
  enables->interrupts = mmio_region_read32(
      i3c->base_addr, (ptrdiff_t)intr_regs[enables->group].status_en);
  return kDifOk;
}

// Set the interrupt status enables within a group.
dif_result_t dif_i3c_intr_status_enable_set(
    const dif_i3c_t *i3c, const dif_i3c_interrupts_t *enables) {
  // There is no STATUS_ENABLE register for the Standby Controller Interrupt
  // group.
  if (enables == NULL || group_invalid(enables->group) ||
      intr_regs[enables->group].status_en == ~0u) {
    return kDifBadArg;
  }
  mmio_region_write32(i3c->base_addr,
                      (ptrdiff_t)intr_regs[enables->group].status_en,
                      enables->interrupts);
  return kDifOk;
}

// Return the current interrupt signal enables for a group.
dif_result_t dif_i3c_intr_signal_enable_get(const dif_i3c_t *i3c,
                                            dif_i3c_interrupts_t *enables) {
  if (enables == NULL || group_invalid(enables->group)) {
    return kDifBadArg;
  }
  enables->interrupts = mmio_region_read32(
      i3c->base_addr, (ptrdiff_t)intr_regs[enables->group].signal_en);
  return kDifOk;
}

// Set the interrupt signal enables for a group.
dif_result_t dif_i3c_intr_signal_enable_set(
    const dif_i3c_t *i3c, const dif_i3c_interrupts_t *enables) {
  if (enables == NULL || group_invalid(enables->group)) {
    return kDifBadArg;
  }
  mmio_region_write32(i3c->base_addr,
                      (ptrdiff_t)intr_regs[enables->group].signal_en,
                      enables->interrupts);
  return kDifOk;
}

// Return the 'force interrupt' signals for a group.
dif_result_t dif_i3c_intr_force_get(const dif_i3c_t *i3c,
                                    dif_i3c_interrupts_t *force) {
  if (force == NULL || group_invalid(force->group)) {
    return kDifBadArg;
  }
  force->interrupts = mmio_region_read32(
      i3c->base_addr, (ptrdiff_t)intr_regs[force->group].force);
  return kDifOk;
}

// Set the 'force interrupt' signals for a group.
dif_result_t dif_i3c_intr_force_set(const dif_i3c_t *i3c,
                                    const dif_i3c_interrupts_t *force) {
  if (force == NULL || group_invalid(force->group)) {
    return kDifBadArg;
  }
  mmio_region_write32(i3c->base_addr, (ptrdiff_t)intr_regs[force->group].force,
                      force->interrupts);
  return kDifOk;
}

// Determine the number of data bytes associated with a Command Descriptor.
dif_result_t dif_i3c_cmd_data_length(const dif_i3c_cmd_desc_t *cmd,
                                     uint16_t *len) {
  if (cmd == NULL || len == NULL) {
    return kDifBadArg;
  }

  // Ascertain the data length.
  switch (cmd->imm.cmd_attr) {
    case kDifI3CCmdAttr_Immediate:
      *len = (uint16_t)((cmd->imm.dtt >= 5) ? cmd->imm.dtt - 5 : cmd->imm.dtt);
      break;
    case kDifI3CCmdAttr_Regular:
      *len = cmd->reg.data_length;
      break;
    case kDifI3CCmdAttr_Combo:
      // TODO: *len = ;
      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}
