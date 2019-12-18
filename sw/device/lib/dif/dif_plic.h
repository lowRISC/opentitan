// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

/**
 * PLIC IRQ IDs enumeration.
 *
 * Enumeration of all PLIC interrupt source IDs. The IRQ IDs belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum dif_plic_irq_id {
  kDifPlicIrqIdNone = 0,             /**< No IRQ */
  kDifPlicIrqIdGpio0 = 1,            /**< GPIO pin 0. */
  kDifPlicIrqIdGpio1 = 2,            /**< GPIO pin 1. */
  kDifPlicIrqIdGpio2 = 3,            /**< GPIO pin 2. */
  kDifPlicIrqIdGpio3 = 4,            /**< GPIO pin 3. */
  kDifPlicIrqIdGpio4 = 5,            /**< GPIO pin 4. */
  kDifPlicIrqIdGpio5 = 6,            /**< GPIO pin 5. */
  kDifPlicIrqIdGpio6 = 7,            /**< GPIO pin 6. */
  kDifPlicIrqIdGpio7 = 8,            /**< GPIO pin 7. */
  kDifPlicIrqIdGpio8 = 9,            /**< GPIO pin 8. */
  kDifPlicIrqIdGpio9 = 10,           /**< GPIO pin 9. */
  kDifPlicIrqIdGpio10 = 11,          /**< GPIO pin 10. */
  kDifPlicIrqIdGpio11 = 12,          /**< GPIO pin 11. */
  kDifPlicIrqIdGpio12 = 13,          /**< GPIO pin 12. */
  kDifPlicIrqIdGpio13 = 14,          /**< GPIO pin 13. */
  kDifPlicIrqIdGpio14 = 15,          /**< GPIO pin 14. */
  kDifPlicIrqIdGpio15 = 16,          /**< GPIO pin 15. */
  kDifPlicIrqIdGpio16 = 17,          /**< GPIO pin 16. */
  kDifPlicIrqIdGpio17 = 18,          /**< GPIO pin 17. */
  kDifPlicIrqIdGpio18 = 19,          /**< GPIO pin 18. */
  kDifPlicIrqIdGpio19 = 20,          /**< GPIO pin 19. */
  kDifPlicIrqIdGpio20 = 21,          /**< GPIO pin 20. */
  kDifPlicIrqIdGpio21 = 22,          /**< GPIO pin 21. */
  kDifPlicIrqIdGpio22 = 23,          /**< GPIO pin 22. */
  kDifPlicIrqIdGpio23 = 24,          /**< GPIO pin 23. */
  kDifPlicIrqIdGpio24 = 25,          /**< GPIO pin 24. */
  kDifPlicIrqIdGpio25 = 26,          /**< GPIO pin 25. */
  kDifPlicIrqIdGpio26 = 27,          /**< GPIO pin 26. */
  kDifPlicIrqIdGpio27 = 28,          /**< GPIO pin 27. */
  kDifPlicIrqIdGpio28 = 29,          /**< GPIO pin 28. */
  kDifPlicIrqIdGpio29 = 30,          /**< GPIO pin 29. */
  kDifPlicIrqIdGpio30 = 31,          /**< GPIO pin 30. */
  kDifPlicIrqIdGpio31 = 32,          /**< GPIO pin 31. */
  kDifPlicIrqIdUartTxWatermark = 33, /**< UART TX FIFO watermark. */
  kDifPlicIrqIdUartRxWatermark = 34, /**< UART RX FIFO watermark. */
  kDifPlicIrqIdUartTxOverflow = 35,  /**< UART TX FIFO overflow. */
  kDifPlicIrqIdUartRxOverflow = 36,  /**< UART RX FIFO overflow. */
  kDifPlicIrqIdUartRxFrameErr = 37,  /**< UART RX frame error. */
  kDifPlicIrqIdUartRxBreakErr = 38,  /**< UART RX break error. */
  kDifPlicIrqIdUartRxTimeout = 39,   /**< UART RX timeout. */
  kDifPlicIrqIdUartRxParityErr = 40, /**< UART RX parity error. */
  kDifPlicIrqIdSpiDeviceRxF = 41,    /**< SPI RX SRAM FIFO full. */
  kDifPlicIrqIdSpiDeviceRxLvl = 42,  /**< SPI RX SRAM FIFO above the level. */
  kDifPlicIrqIdSpiDeviceTxLvl = 43,  /**< SPI TX SRAM FIFO under the level. */
  kDifPlicIrqIdSpiDeviceRxErr = 44,  /**< SPI MOSI in FwMode has error. */
  kDifPlicIrqIdSpiDeviceRxOverflow = 45,  /**< SPI RX Async FIFO overflow. */
  kDifPlicIrqIdSpiDeviceTxUnderflow = 46, /**< SPI TX Async FIFO underflow. */
  kDifPlicIrqIdFlashCtrlProgEmpty = 47,   /**< Flash prog FIFO empty. */
  kDifPlicIrqIdFlashCtrlProgLvl = 48,   /**< Flash prog FIFO drained to lvl. */
  kDifPlicIrqIdFlashCtrlRdFull = 49,    /**< Flash read FIFO full. */
  kDifPlicIrqIdFlashCtrlRdLvl = 50,     /**< Flash read FIFO filled to lvl. */
  kDifPlicIrqIdFlashCtrlOpDone = 51,    /**< Flash operation complete. */
  kDifPlicIrqIdFlashCtrlOpError = 52,   /**< Flash operation failed with err. */
  kDifPlicIrqIdHmacDone = 53,           /**< HMAC done. */
  kDifPlicIrqIdHmacFifoFull = 54,       /**< HMAC FIFO full. */
  kDifPlicIrqIdHmacErr = 55,            /**< HMAC error. */
  kDifPlicIrqIdAlertHandlerClassA = 56, /**< Alert Handler class A alert. */
  kDifPlicIrqIdAlertHandlerClassB = 57, /**< Alert Handler class B alert. */
  kDifPlicIrqIdAlertHandlerClassC = 58, /**< Alert Handler class C alert. */
  kDifPlicIrqIdAlertHandlerClassD = 59, /**< Alert Handler class D alert. */
  kDifPlicIrqIdNmiGenEsc0 = 60,         /**< NMI Gen escalation interrupt 0. */
  kDifPlicIrqIdNmiGenEsc1 = 61,         /**< NMI Gen escalation interrupt 1. */
  kDifPlicIrqIdNmiGenEsc2 = 62,         /**< NMI Gen escalation interrupt 2. */
  kDifPlicIrqIdNmiGenEsc3 = 63,         /**< NMI Gen escalation interrupt 3. */
  kDifPlicIrqIdLast = kDifPlicIrqIdNmiGenEsc3, /**< The last valid IRQ ID. */
} dif_plic_irq_id_t;

/**
 * PLIC IRQ source peripheral enumeration.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * IRQ source.
 */
typedef enum dif_plic_peripheral {
  kDifPlicPeripheralGpio = 0,     /**< GPIO */
  kDifPlicPeripheralUart,         /**< UART */
  kDifPlicPeripheralSpiDevice,    /**< SPI */
  kDifPlicPeripheralFlashCtrl,    /**< Flash */
  kDifPlicPeripheralHmac,         /**< HMAC */
  kDifPlicPeripheralAlertHandler, /**< Alert handler */
  kDifPlicPeripheralNmiGen,       /**< NMI generator */
  kDifPlicPeripheralCount,        /**< Number of PLIC peripherals */
} dif_plic_peripheral_t;

/**
 * PLIC external interrupt target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access dependent on the target.
 */
typedef enum dif_plic_target {
  kDifPlicTargetIbex0 = 0, /* Ibex CPU */
  kDifPlicTargetCount,
} dif_plic_target_t;

/**
 * Generic enable/disable enumeration.
 *
 * Enumeration used to enable/disable bits, flags, ...
 */
typedef enum dif_plic_enable {
  kDifPlicEnable = 0,
  kDifPlicDisable,
} dif_plic_enable_t;

/**
 * Generic set/unset enumeration.
 *
 * Enumeration used to set/unset, or get the state of bits,flags ...
 */
typedef enum dif_plic_flag {
  kDifPlicSet = 0,
  kDifPlicUnset,
} dif_plic_flag_t;

/**
 * PLIC CC (IRQ claim register data).
 *
 * Data that is populated by the PLIC DIF when interrupt is claimed. Is used by
 * the PLIC DIF consumers to establish the IRQ source ID, and the peripheral
 * that asserted this IRQ.
 */
typedef struct dif_irq_claim_data {
  dif_plic_peripheral_t peripheral; /**< Peripheral that interrupted */
  dif_plic_irq_id_t source;         /**< IRQ type */
  ptrdiff_t cc_offset;              /**< Target specifc CC offset */
} dif_irq_claim_data_t;

/**
 * PLIC instance state.
 *
 * PLIC persistent data that is required by all the PLIC API.
 */
typedef struct dif_plic {
  mmio_region_t base_addr; /**< PLIC instance base address */
} dif_plic_t;

/**
 * Initialises an instance of PLIC.
 *
 * Information that must be retained, and is required to program PLIC, shall
 * be stored in @p arg2.
 *
 * @param base_addr Base address of an instance of the PLIC IP block
 * @param plic PLIC state data
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_init(mmio_region_t base_addr, dif_plic_t *plic);

/**
 * Enables/disables handling of IRQ source in PLIC.
 *
 * This operation does not affect the IRQ generation in the peripherals, which
 * must be configured in a corresponding peripheral itself.
 * @param plic PLIC state data
 * @param irq Interrupt Source ID
 * @param target Target to enable the IRQ for
 * @param enable Enable/disable the IRQ handling
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_enable_set(const dif_plic_t *plic, dif_plic_irq_id_t irq,
                             dif_plic_target_t target,
                             dif_plic_enable_t enable);

/**
 * Sets the IRQ trigger type (edge/level).
 *
 * Sets the behaviour of the Interrupt Gateway for a particular IRQ to be edge
 * or level triggered.
 * @param plic PLIC state data
 * @param irq Interrupt source ID
 * @param enable Enable for the edge triggered, disable for level triggered IRQs
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_trigger_type_set(const dif_plic_t *plic,
                                   dif_plic_irq_id_t irq,
                                   dif_plic_enable_t enable);

/**
 * Sets IRQ source priority (0-3).
 *
 * In order for PLIC to set a CC register and assert the external interrupt line
 * to the target (Ibex, ...), the priority of an IRQ source must be higher than
 * the threshold for this source.
 * @param plic PLIC state data
 * @param irq Interrupt source ID
 * @param priority Priority to be set
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_priority_set(const dif_plic_t *plic, dif_plic_irq_id_t irq,
                               uint32_t priority);

/**
 * Sets the target priority threshold.
 *
 * Sets the target priority threshold. PLIC will only interrupt a target when
 * IRQ source priority is set higher than the priority threshold for the
 * corresponding target.
 * @param plic PLIC state data
 * @param target Target to set the IRQ priority threshold for
 * @param threshold IRQ priority threshold to be set
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_target_threshold_set(const dif_plic_t *plic,
                                   dif_plic_target_t target,
                                   uint32_t threshold);

/**
 * Checks the Interrupt Pending bit.
 *
 * Gets the status of the PLIC Interrupt Pending register bit for a specific IRQ
 * source.
 * @param plic PLIC state data
 * @param irq Interrupt source ID
 * @param status Flag indicating whether the IRQ pending bit is set in PLIC
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_pending_status_get(const dif_plic_t *plic,
                                     dif_plic_irq_id_t irq,
                                     dif_plic_flag_t *status);

/**
 * Claims an IRQ and gets the information about the source.
 *
 * Claims an IRQ and returns the IRQ related data to the caller. This function
 * reads a target specific CC register. dif_plic_irq_complete must be called
 * after the claimed IRQ has been serviced.
 *
 * @param plic PLIC state data
 * @param target Target that claimed the IRQ
 * @param claim_data Data that describes the origin and belonging of the IRQ.
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_claim(const dif_plic_t *plic, dif_plic_target_t target,
                        dif_irq_claim_data_t *claim_data);

/**
 * Completes the claimed IRQ.
 *
 * Finishes servicing of the claimed IRQ by writing the IRQ source ID back to a
 * target specific CC register. This function must be called after
 * dif_plic_claim_irq, when a caller has finished servicing the IRQ.
 *
 * @param plic PLIC state data
 * @param complete_data Previously claimed IRQ data that is used to signal PLIC
 *                      of the IRQ servicing completion.
 * @return true if the function was successful, false otherwise
 */
bool dif_plic_irq_complete(const dif_plic_t *plic,
                           const dif_irq_claim_data_t *complete_data);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PLIC_H_
