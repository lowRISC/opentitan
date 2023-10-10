
#ifndef ALSAQR_PERIPH_PADFRAME_H
#define ALSAQR_PERIPH_PADFRAME_H
#include <stdint.h>

#define ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS 0x1A104000

#ifndef ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS
#error "ALSAQR_PERIPH_PADFRAME_BASE_ADDRESS is not defined. Set this token to the configuration base address of your padframe before you include this header file."
#endif



/**
 * Sets the chip2pad pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_00_group_CAN0_port_CAN_TX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_00_group_GPIO_B_port_GPIO0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_00_group_UART_CORE_port_UART_TX = 3,
} alsaqr_periph_padframe_periphs_a_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_00_mux_set(alsaqr_periph_padframe_periphs_a_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_00_mux_sel_t alsaqr_periph_padframe_periphs_a_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_01_group_CAN0_port_CAN_RX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_01_group_GPIO_B_port_GPIO1 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_01_group_UART_CORE_port_UART_RX = 3,
} alsaqr_periph_padframe_periphs_a_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_01_mux_set(alsaqr_periph_padframe_periphs_a_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_01_mux_sel_t alsaqr_periph_padframe_periphs_a_01_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_02
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_02
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_02
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_02
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_02
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_02_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_02
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_02_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_group_CAN1_port_CAN_TX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_group_GPIO_B_port_GPIO2 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_group_QSPI_LINUX_port_QSPI_SCK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_group_SDIO0_port_SDIO_DATA0 = 4,
} alsaqr_periph_padframe_periphs_a_02_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_02.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_02_mux_set(alsaqr_periph_padframe_periphs_a_02_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_02.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_02_mux_sel_t alsaqr_periph_padframe_periphs_a_02_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_03
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_03
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_03
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_03
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_03
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_03_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_03
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_03_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_group_CAN1_port_CAN_RX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_group_GPIO_B_port_GPIO3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_group_QSPI_LINUX_port_QSPI_CSN = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_group_SDIO0_port_SDIO_DATA1 = 4,
} alsaqr_periph_padframe_periphs_a_03_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_03.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_03_mux_set(alsaqr_periph_padframe_periphs_a_03_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_03.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_03_mux_sel_t alsaqr_periph_padframe_periphs_a_03_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_04
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_04
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_04
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_04
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_04
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_04_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_04
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_04_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_group_FLL_SOC_port_CLK_SOC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_group_GPIO_B_port_GPIO4 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_group_QSPI_LINUX_port_QSPI_SD0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_group_SDIO0_port_SDIO_DATA2 = 4,
} alsaqr_periph_padframe_periphs_a_04_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_04.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_04_mux_set(alsaqr_periph_padframe_periphs_a_04_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_04.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_04_mux_sel_t alsaqr_periph_padframe_periphs_a_04_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_05
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_05
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_05
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_05
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_05
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_05_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_05
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_05_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_group_GPIO_B_port_GPIO5 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_group_QSPI_LINUX_port_QSPI_SD1 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_group_SDIO0_port_SDIO_DATA3 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_group_USART1_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_a_05_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_05.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_05_mux_set(alsaqr_periph_padframe_periphs_a_05_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_05.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_05_mux_sel_t alsaqr_periph_padframe_periphs_a_05_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_06
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_06
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_06
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_06
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_06
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_06_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_06
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_06_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_group_GPIO_B_port_GPIO6 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_group_QSPI_LINUX_port_QSPI_SD2 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_group_SDIO0_port_SDIO_CLK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_group_USART1_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_a_06_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_06.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_06_mux_set(alsaqr_periph_padframe_periphs_a_06_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_06.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_06_mux_sel_t alsaqr_periph_padframe_periphs_a_06_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_07
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_07
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_07
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_07
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_07
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_07_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_07
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_07_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_group_GPIO_B_port_GPIO7 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_group_QSPI_LINUX_port_QSPI_SD3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_group_SDIO0_port_SDIO_CMD = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_group_USART1_port_UART_RTS = 4,
} alsaqr_periph_padframe_periphs_a_07_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_07.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_07_mux_set(alsaqr_periph_padframe_periphs_a_07_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_07.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_07_mux_sel_t alsaqr_periph_padframe_periphs_a_07_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_08
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_08
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_08
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_08
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_08
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_08_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_08
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_08_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_group_GPIO_B_port_GPIO8 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_group_I2C0_port_I2C_SCL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_group_PWM0_port_PWM0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_group_USART1_port_UART_CTS = 4,
} alsaqr_periph_padframe_periphs_a_08_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_08.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_08_mux_set(alsaqr_periph_padframe_periphs_a_08_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_08.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_08_mux_sel_t alsaqr_periph_padframe_periphs_a_08_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_09
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_09
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_09
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_09
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_09
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_09_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_09
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_09_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_group_GPIO_B_port_GPIO9 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_group_I2C0_port_I2C_SDA = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_group_PWM0_port_PWM1 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_group_SDIO1_port_SDIO_DATA0 = 4,
} alsaqr_periph_padframe_periphs_a_09_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_09.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_09_mux_set(alsaqr_periph_padframe_periphs_a_09_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_09.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_09_mux_sel_t alsaqr_periph_padframe_periphs_a_09_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_10
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_10
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_10
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_10
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_10
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_10_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_10
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_10_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_group_GPIO_B_port_GPIO10 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_group_PWM0_port_PWM2 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_group_PWM1_port_PWM0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_group_SDIO1_port_SDIO_DATA1 = 4,
} alsaqr_periph_padframe_periphs_a_10_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_10.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_10_mux_set(alsaqr_periph_padframe_periphs_a_10_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_10.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_10_mux_sel_t alsaqr_periph_padframe_periphs_a_10_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_11
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_11
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_11
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_11
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_11
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_11_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_11
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_11_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_group_GPIO_B_port_GPIO11 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_group_PWM0_port_PWM3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_group_PWM1_port_PWM1 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_group_SDIO1_port_SDIO_DATA2 = 4,
} alsaqr_periph_padframe_periphs_a_11_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_11.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_11_mux_set(alsaqr_periph_padframe_periphs_a_11_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_11.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_11_mux_sel_t alsaqr_periph_padframe_periphs_a_11_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_12
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_12
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_12
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_12
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_12
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_12_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_12
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_12_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_group_GPIO_B_port_GPIO12 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_group_I2C0_port_I2C_SCL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_group_PWM1_port_PWM2 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_group_SDIO1_port_SDIO_DATA3 = 4,
} alsaqr_periph_padframe_periphs_a_12_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_12.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_12_mux_set(alsaqr_periph_padframe_periphs_a_12_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_12.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_12_mux_sel_t alsaqr_periph_padframe_periphs_a_12_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_13
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_13
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_13
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_13
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_13
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_13_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_13
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_13_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_group_GPIO_B_port_GPIO13 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_group_I2C0_port_I2C_SDA = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_group_PWM1_port_PWM3 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_group_SDIO1_port_SDIO_CLK = 4,
} alsaqr_periph_padframe_periphs_a_13_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_13.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_13_mux_set(alsaqr_periph_padframe_periphs_a_13_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_13.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_13_mux_sel_t alsaqr_periph_padframe_periphs_a_13_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_14
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_14
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_14
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_14
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_14
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_14_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_14
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_14_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_group_GPIO_B_port_GPIO14 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_group_SDIO1_port_SDIO_CMD = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_group_SPI0_port_SPI_SCK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_group_UART0_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_a_14_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_14.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_14_mux_set(alsaqr_periph_padframe_periphs_a_14_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_14.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_14_mux_sel_t alsaqr_periph_padframe_periphs_a_14_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_15
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_15
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_15
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_15
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_15
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_15_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_15
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_15_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_group_ETH_port_ETH_RST = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_group_GPIO_B_port_GPIO15 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_group_SPI0_port_SPI_CS0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_group_UART0_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_a_15_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_15.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_15_mux_set(alsaqr_periph_padframe_periphs_a_15_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_15.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_15_mux_sel_t alsaqr_periph_padframe_periphs_a_15_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_16
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_16
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_16
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_16
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_16
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_16_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_16
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_16_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_group_ETH_port_ETH_RXCK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_group_GPIO_B_port_GPIO16 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_group_I2C1_port_I2C_SCL = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_group_SPI0_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_a_16_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_16.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_16_mux_set(alsaqr_periph_padframe_periphs_a_16_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_16.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_16_mux_sel_t alsaqr_periph_padframe_periphs_a_16_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_17
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_17
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_17
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_17
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_17
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_17_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_17
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_17_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_group_ETH_port_ETH_RXCTL = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_group_GPIO_B_port_GPIO17 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_group_I2C1_port_I2C_SDA = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_group_SPI0_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_a_17_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_17.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_17_mux_set(alsaqr_periph_padframe_periphs_a_17_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_17.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_17_mux_sel_t alsaqr_periph_padframe_periphs_a_17_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_18
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_18
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_18
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_18
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_18
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_18_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_18
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_18_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_group_CAM0_port_CAM_PCLK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_group_ETH_port_ETH_RXD0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_group_GPIO_B_port_GPIO18 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_group_SPI2_port_SPI_SCK = 4,
} alsaqr_periph_padframe_periphs_a_18_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_18.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_18_mux_set(alsaqr_periph_padframe_periphs_a_18_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_18.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_18_mux_sel_t alsaqr_periph_padframe_periphs_a_18_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_19
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_19
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_19
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_19
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_19
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_19_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_19
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_19_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_group_CAM0_port_CAM_VSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_group_ETH_port_ETH_RXD1 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_group_GPIO_B_port_GPIO19 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_group_SPI2_port_SPI_CS0 = 4,
} alsaqr_periph_padframe_periphs_a_19_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_19.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_19_mux_set(alsaqr_periph_padframe_periphs_a_19_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_19.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_19_mux_sel_t alsaqr_periph_padframe_periphs_a_19_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_20
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_20
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_20
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_20
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_20
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_20_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_20
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_20_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_group_CAM0_port_CAM_HSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_group_ETH_port_ETH_RXD2 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_group_GPIO_B_port_GPIO20 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_group_SPI2_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_a_20_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_20.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_20_mux_set(alsaqr_periph_padframe_periphs_a_20_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_20.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_20_mux_sel_t alsaqr_periph_padframe_periphs_a_20_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_21
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_21
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_21
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_21
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_21
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_21_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_21
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_21_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_group_CAM0_port_CAM_DATA0_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_group_ETH_port_ETH_RXD3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_group_GPIO_B_port_GPIO21 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_group_SPI2_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_a_21_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_21.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_21_mux_set(alsaqr_periph_padframe_periphs_a_21_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_21.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_21_mux_sel_t alsaqr_periph_padframe_periphs_a_21_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_22
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_22
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_22
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_22
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_22
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_22_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_22
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_22_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_group_CAM0_port_CAM_DATA1_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_group_ETH_port_ETH_TXCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_group_GPIO_B_port_GPIO22 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_group_SPI3_port_SPI_SCK = 4,
} alsaqr_periph_padframe_periphs_a_22_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_22.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_22_mux_set(alsaqr_periph_padframe_periphs_a_22_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_22.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_22_mux_sel_t alsaqr_periph_padframe_periphs_a_22_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_23
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_23
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_23
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_23
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_23
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_23_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_23
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_23_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_group_CAM0_port_CAM_DATA2_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_group_ETH_port_ETH_TXCTL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_group_GPIO_B_port_GPIO23 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_group_SPI3_port_SPI_CS0 = 4,
} alsaqr_periph_padframe_periphs_a_23_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_23.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_23_mux_set(alsaqr_periph_padframe_periphs_a_23_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_23.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_23_mux_sel_t alsaqr_periph_padframe_periphs_a_23_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_24
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_24
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_24
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_24
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_24
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_24_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_24
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_24_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_group_CAM0_port_CAM_DATA3_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_group_ETH_port_ETH_TXD0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_group_GPIO_B_port_GPIO24 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_group_SPI3_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_a_24_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_24.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_24_mux_set(alsaqr_periph_padframe_periphs_a_24_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_24.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_24_mux_sel_t alsaqr_periph_padframe_periphs_a_24_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_25
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_25
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_25
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_25
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_25
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_25_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_25
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_25_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_group_CAM0_port_CAM_DATA4_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_group_ETH_port_ETH_TXD1 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_group_GPIO_B_port_GPIO25 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_group_SPI3_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_a_25_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_25.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_25_mux_set(alsaqr_periph_padframe_periphs_a_25_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_25.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_25_mux_sel_t alsaqr_periph_padframe_periphs_a_25_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_26
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_26
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_26
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_26
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_26
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_26_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_26
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_26_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_group_CAM0_port_CAM_DATA5_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_group_ETH_port_ETH_TXD2 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_group_GPIO_B_port_GPIO26 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_group_UART0_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_a_26_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_26.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_26_mux_set(alsaqr_periph_padframe_periphs_a_26_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_26.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_26_mux_sel_t alsaqr_periph_padframe_periphs_a_26_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_27
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_27
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_27
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_27
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_27
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_27_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_27
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_27_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_group_CAM0_port_CAM_DATA6_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_group_ETH_port_ETH_TXD3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_group_GPIO_B_port_GPIO27 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_group_UART0_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_a_27_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_27.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_27_mux_set(alsaqr_periph_padframe_periphs_a_27_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_27.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_27_mux_sel_t alsaqr_periph_padframe_periphs_a_27_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_28
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_28
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_28
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_28
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_28
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_28_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_28
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_28_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_group_CAM0_port_CAM_DATA7_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_group_ETH_port_ETH_MDIO = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_group_GPIO_B_port_GPIO28 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_group_I2C1_port_I2C_SCL = 4,
} alsaqr_periph_padframe_periphs_a_28_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_28.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_28_mux_set(alsaqr_periph_padframe_periphs_a_28_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_28.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_28_mux_sel_t alsaqr_periph_padframe_periphs_a_28_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_29
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_29
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_29
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_29
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_29
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_29_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_29
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_29_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_group_ETH_port_ETH_MDC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_group_FLL_SOC_port_CLK_SOC = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_group_GPIO_B_port_GPIO29 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_group_I2C1_port_I2C_SDA = 4,
} alsaqr_periph_padframe_periphs_a_29_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_29.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_29_mux_set(alsaqr_periph_padframe_periphs_a_29_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_29.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_29_mux_sel_t alsaqr_periph_padframe_periphs_a_29_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_00_group_GPIO_B_port_GPIO0 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_00_group_SDIO1_port_SDIO_DATA0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_00_group_UART0_port_UART_TX = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_00_group_USART0_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_b_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_00_mux_set(alsaqr_periph_padframe_periphs_b_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_00_mux_sel_t alsaqr_periph_padframe_periphs_b_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_group_GPIO_B_port_GPIO1 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_group_I2C1_port_I2C_SCL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_group_SDIO1_port_SDIO_DATA1 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_group_UART0_port_UART_RX = 4,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_01_group_USART0_port_UART_RX = 5,
} alsaqr_periph_padframe_periphs_b_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_01_mux_set(alsaqr_periph_padframe_periphs_b_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_01_mux_sel_t alsaqr_periph_padframe_periphs_b_01_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_02
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_02
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_02
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_02
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_02
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_02_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_02
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_02_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_02_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_02_group_GPIO_B_port_GPIO2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_02_group_I2C1_port_I2C_SDA = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_02_group_SDIO1_port_SDIO_DATA2 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_02_group_USART0_port_UART_RTS = 4,
} alsaqr_periph_padframe_periphs_b_02_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_02.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_02_mux_set(alsaqr_periph_padframe_periphs_b_02_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_02.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_02_mux_sel_t alsaqr_periph_padframe_periphs_b_02_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_03
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_03
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_03
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_03
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_03
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_03_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_03
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_03_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_03_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_03_group_GPIO_B_port_GPIO3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_03_group_SDIO1_port_SDIO_DATA3 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_03_group_USART0_port_UART_CTS = 3,
} alsaqr_periph_padframe_periphs_b_03_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_03.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_03_mux_set(alsaqr_periph_padframe_periphs_b_03_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_03.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_03_mux_sel_t alsaqr_periph_padframe_periphs_b_03_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_04
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_04
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_04
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_04
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_04
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_04_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_04
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_04_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_04_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_04_group_GPIO_B_port_GPIO4 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_04_group_SDIO1_port_SDIO_CLK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_04_group_SPI4_port_SPI_SCK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_04_group_SPI5_port_SPI_SCK = 4,
} alsaqr_periph_padframe_periphs_b_04_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_04.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_04_mux_set(alsaqr_periph_padframe_periphs_b_04_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_04.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_04_mux_sel_t alsaqr_periph_padframe_periphs_b_04_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_05
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_05
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_05
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_05
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_05
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_05_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_05
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_05_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_05_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_05_group_GPIO_B_port_GPIO5 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_05_group_SDIO1_port_SDIO_CMD = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_05_group_SPI4_port_SPI_CS0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_05_group_SPI5_port_SPI_CS0 = 4,
} alsaqr_periph_padframe_periphs_b_05_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_05.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_05_mux_set(alsaqr_periph_padframe_periphs_b_05_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_05.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_05_mux_sel_t alsaqr_periph_padframe_periphs_b_05_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_06
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_06
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_06
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_06
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_06
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_06
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_06_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_06
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_06_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_06_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_06_group_GPIO_B_port_GPIO6 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_06_group_SPI0_port_SPI_SCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_06_group_SPI4_port_SPI_MISO = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_06_group_SPI5_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_b_06_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_06.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_06_mux_set(alsaqr_periph_padframe_periphs_b_06_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_06.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_06_mux_sel_t alsaqr_periph_padframe_periphs_b_06_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_07
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_07
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_07
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_07
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_07
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_07
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_07_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_07
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_07_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_07_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_07_group_GPIO_B_port_GPIO7 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_07_group_SPI0_port_SPI_CS0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_07_group_SPI4_port_SPI_MOSI = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_07_group_SPI5_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_b_07_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_07.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_07_mux_set(alsaqr_periph_padframe_periphs_b_07_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_07.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_07_mux_sel_t alsaqr_periph_padframe_periphs_b_07_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_08
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_08
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_08
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_08
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_08
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_08
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_08_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_08
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_08_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_08_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_08_group_GPIO_B_port_GPIO8 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_08_group_I2C2_port_I2C_SCL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_08_group_I2C3_port_I2C_SCL = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_08_group_SPI0_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_b_08_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_08.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_08_mux_set(alsaqr_periph_padframe_periphs_b_08_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_08.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_08_mux_sel_t alsaqr_periph_padframe_periphs_b_08_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_09
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_09
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_09
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_09
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_09
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_09
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_09_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_09
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_09_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_09_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_09_group_GPIO_B_port_GPIO9 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_09_group_I2C2_port_I2C_SDA = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_09_group_I2C3_port_I2C_SDA = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_09_group_SPI0_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_b_09_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_09.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_09_mux_set(alsaqr_periph_padframe_periphs_b_09_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_09.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_09_mux_sel_t alsaqr_periph_padframe_periphs_b_09_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_10
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_10
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_10
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_10
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_10
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_10
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_10_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_10
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_10_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_10_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_10_group_GPIO_B_port_GPIO10 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_10_group_SPI6_port_SPI_SCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_10_group_SPI7_port_SPI_SCK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_10_group_USART0_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_b_10_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_10.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_10_mux_set(alsaqr_periph_padframe_periphs_b_10_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_10.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_10_mux_sel_t alsaqr_periph_padframe_periphs_b_10_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_11
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_11
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_11
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_11
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_11
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_11
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_11_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_11
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_11_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_11_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_11_group_GPIO_B_port_GPIO11 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_11_group_SPI6_port_SPI_CS0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_11_group_SPI7_port_SPI_MISO = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_11_group_USART0_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_b_11_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_11.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_11_mux_set(alsaqr_periph_padframe_periphs_b_11_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_11.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_11_mux_sel_t alsaqr_periph_padframe_periphs_b_11_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_12
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_12
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_12
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_12
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_12
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_12
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_12_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_12
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_12_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_12_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_12_group_GPIO_B_port_GPIO12 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_12_group_SPI6_port_SPI_MISO = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_12_group_SPI7_port_SPI_MOSI = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_12_group_USART0_port_UART_RTS = 4,
} alsaqr_periph_padframe_periphs_b_12_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_12.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_12_mux_set(alsaqr_periph_padframe_periphs_b_12_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_12.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_12_mux_sel_t alsaqr_periph_padframe_periphs_b_12_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_13
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_13
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_13
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_13
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_13
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_13
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_13_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_13
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_13_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_13_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_13_group_GPIO_B_port_GPIO13 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_13_group_SPI6_port_SPI_MOSI = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_13_group_SPI7_port_SPI_CS0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_13_group_USART0_port_UART_CTS = 4,
} alsaqr_periph_padframe_periphs_b_13_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_13.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_13_mux_set(alsaqr_periph_padframe_periphs_b_13_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_13.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_13_mux_sel_t alsaqr_periph_padframe_periphs_b_13_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_14
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_14
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_14
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_14
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_14
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_14
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_14_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_14
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_14_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_14_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_14_group_GPIO_B_port_GPIO14 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_14_group_SPI4_port_SPI_SCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_14_group_SPI7_port_SPI_CS1 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_14_group_USART2_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_b_14_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_14.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_14_mux_set(alsaqr_periph_padframe_periphs_b_14_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_14.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_14_mux_sel_t alsaqr_periph_padframe_periphs_b_14_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_15
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_15
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_15
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_15
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_15
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_15
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_15_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_15
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_15_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_15_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_15_group_GPIO_B_port_GPIO15 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_15_group_I2C4_port_I2C_SCL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_15_group_SPI4_port_SPI_CS0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_15_group_USART2_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_b_15_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_15.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_15_mux_set(alsaqr_periph_padframe_periphs_b_15_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_15.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_15_mux_sel_t alsaqr_periph_padframe_periphs_b_15_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_16
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_16
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_16
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_16
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_16
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_16
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_16_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_16
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_16_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_16_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_16_group_GPIO_B_port_GPIO16 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_16_group_I2C4_port_I2C_SDA = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_16_group_SPI4_port_SPI_MISO = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_16_group_USART2_port_UART_RTS = 4,
} alsaqr_periph_padframe_periphs_b_16_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_16.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_16_mux_set(alsaqr_periph_padframe_periphs_b_16_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_16.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_16_mux_sel_t alsaqr_periph_padframe_periphs_b_16_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_17
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_17
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_17
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_17
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_17
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_17
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_17_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_17
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_17_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_17_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_17_group_GPIO_B_port_GPIO17 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_17_group_SPI4_port_SPI_MOSI = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_17_group_UART1_port_UART_TX = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_17_group_USART2_port_UART_CTS = 4,
} alsaqr_periph_padframe_periphs_b_17_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_17.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_17_mux_set(alsaqr_periph_padframe_periphs_b_17_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_17.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_17_mux_sel_t alsaqr_periph_padframe_periphs_b_17_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_18
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_18
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_18
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_18
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_18
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_18
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_18_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_18
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_18_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_18_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_18_group_GPIO_B_port_GPIO18 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_18_group_SPI2_port_SPI_SCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_18_group_UART1_port_UART_RX = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_18_group_USART3_port_UART_TX = 4,
} alsaqr_periph_padframe_periphs_b_18_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_18.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_18_mux_set(alsaqr_periph_padframe_periphs_b_18_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_18.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_18_mux_sel_t alsaqr_periph_padframe_periphs_b_18_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_19
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_19
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_19
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_19
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_19
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_19
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_19_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_19
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_19_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_GPIO_B_port_GPIO19 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_SPI2_port_SPI_CS0 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_USART1_port_UART_TX = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_USART3_port_UART_RX = 4,
} alsaqr_periph_padframe_periphs_b_19_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_19.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_19_mux_set(alsaqr_periph_padframe_periphs_b_19_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_19.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_19_mux_sel_t alsaqr_periph_padframe_periphs_b_19_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_20
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_20
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_20
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_20
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_20
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_20
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_20_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_20
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_20_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_GPIO_B_port_GPIO20 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_SPI2_port_SPI_MISO = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_USART1_port_UART_RX = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_USART3_port_UART_RTS = 4,
} alsaqr_periph_padframe_periphs_b_20_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_20.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_20_mux_set(alsaqr_periph_padframe_periphs_b_20_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_20.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_20_mux_sel_t alsaqr_periph_padframe_periphs_b_20_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_21
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_21
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_21
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_21
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_21
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_21
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_21_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_21
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_21_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_GPIO_B_port_GPIO21 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_SPI2_port_SPI_MOSI = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_USART1_port_UART_RTS = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_USART3_port_UART_CTS = 4,
} alsaqr_periph_padframe_periphs_b_21_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_21.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_21_mux_set(alsaqr_periph_padframe_periphs_b_21_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_21.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_21_mux_sel_t alsaqr_periph_padframe_periphs_b_21_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_22
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_22
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_22
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_22
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_22
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_22
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_22_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_22
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_22_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_GPIO_B_port_GPIO22 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_SPI3_port_SPI_SCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_SPI8_port_SPI_SCK = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_USART1_port_UART_CTS = 4,
} alsaqr_periph_padframe_periphs_b_22_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_22.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_22_mux_set(alsaqr_periph_padframe_periphs_b_22_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_22.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_22_mux_sel_t alsaqr_periph_padframe_periphs_b_22_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_23
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_23
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_23
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_23
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_23
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_23
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_23_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_23
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_23_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_ETH_port_ETH_RST = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_GPIO_B_port_GPIO23 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_SPI3_port_SPI_CS0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_SPI8_port_SPI_CS0 = 4,
} alsaqr_periph_padframe_periphs_b_23_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_23.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_23_mux_set(alsaqr_periph_padframe_periphs_b_23_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_23.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_23_mux_sel_t alsaqr_periph_padframe_periphs_b_23_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_24
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_24
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_24
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_24
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_24
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_24
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_24_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_24
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_24_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_ETH_port_ETH_RXCK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_GPIO_B_port_GPIO24 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_SPI3_port_SPI_MISO = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_SPI8_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_b_24_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_24.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_24_mux_set(alsaqr_periph_padframe_periphs_b_24_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_24.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_24_mux_sel_t alsaqr_periph_padframe_periphs_b_24_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_25
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_25
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_25
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_25
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_25
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_25
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_25_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_25
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_25_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_ETH_port_ETH_RXCTL = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_GPIO_B_port_GPIO25 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_SPI3_port_SPI_MOSI = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_SPI8_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_b_25_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_25.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_25_mux_set(alsaqr_periph_padframe_periphs_b_25_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_25.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_25_mux_sel_t alsaqr_periph_padframe_periphs_b_25_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_26
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_26
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_26
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_26
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_26
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_26
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_26_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_26
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_26_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_26_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_26_group_ETH_port_ETH_RXD0 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_26_group_GPIO_B_port_GPIO26 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_26_group_SPI9_port_SPI_SCK = 3,
} alsaqr_periph_padframe_periphs_b_26_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_26.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_26_mux_set(alsaqr_periph_padframe_periphs_b_26_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_26.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_26_mux_sel_t alsaqr_periph_padframe_periphs_b_26_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_27
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_27
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_27
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_27
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_27
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_27
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_27_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_27
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_27_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_27_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_27_group_ETH_port_ETH_RXD1 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_27_group_GPIO_B_port_GPIO27 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_27_group_SPI9_port_SPI_CS0 = 3,
} alsaqr_periph_padframe_periphs_b_27_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_27.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_27_mux_set(alsaqr_periph_padframe_periphs_b_27_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_27.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_27_mux_sel_t alsaqr_periph_padframe_periphs_b_27_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_28
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_28
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_28
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_28
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_28
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_28
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_28_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_28
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_28_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_28_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_28_group_ETH_port_ETH_RXD2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_28_group_GPIO_B_port_GPIO28 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_28_group_SPI9_port_SPI_MISO = 3,
} alsaqr_periph_padframe_periphs_b_28_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_28.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_28_mux_set(alsaqr_periph_padframe_periphs_b_28_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_28.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_28_mux_sel_t alsaqr_periph_padframe_periphs_b_28_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_29
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_29
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_29
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_29
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_29
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_29
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_29_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_29
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_29_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_29_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_29_group_ETH_port_ETH_RXD3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_29_group_GPIO_B_port_GPIO29 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_29_group_SPI9_port_SPI_MOSI = 3,
} alsaqr_periph_padframe_periphs_b_29_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_29.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_29_mux_set(alsaqr_periph_padframe_periphs_b_29_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_29.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_29_mux_sel_t alsaqr_periph_padframe_periphs_b_29_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_30
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_30
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_30
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_30
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_30
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_30_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_30
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_30_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_group_CAN1_port_CAN_TX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_group_ETH_port_ETH_TXCK = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_group_GPIO_B_port_GPIO30 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_group_SPI10_port_SPI_SCK = 4,
} alsaqr_periph_padframe_periphs_b_30_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_30.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_30_mux_set(alsaqr_periph_padframe_periphs_b_30_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_30.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_30_mux_sel_t alsaqr_periph_padframe_periphs_b_30_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_31
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_31
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_31
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_31
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_31
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_31_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_31
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_31_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_group_CAN1_port_CAN_RX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_group_ETH_port_ETH_TXCTL = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_group_GPIO_B_port_GPIO31 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_group_SPI10_port_SPI_CS0 = 4,
} alsaqr_periph_padframe_periphs_b_31_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_31.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_31_mux_set(alsaqr_periph_padframe_periphs_b_31_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_31.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_31_mux_sel_t alsaqr_periph_padframe_periphs_b_31_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_32
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_32
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_32
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_32
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_32
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_32_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_32
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_32_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_group_ETH_port_ETH_TXD0 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_group_GPIO_B_port_GPIO32 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_group_PWM1_port_PWM0 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_group_SPI10_port_SPI_MISO = 4,
} alsaqr_periph_padframe_periphs_b_32_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_32.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_32_mux_set(alsaqr_periph_padframe_periphs_b_32_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_32.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_32_mux_sel_t alsaqr_periph_padframe_periphs_b_32_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_33
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_33
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_33
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_33
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_33
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_33_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_33
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_33_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_group_ETH_port_ETH_TXD1 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_group_GPIO_B_port_GPIO33 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_group_PWM1_port_PWM1 = 3,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_group_SPI10_port_SPI_MOSI = 4,
} alsaqr_periph_padframe_periphs_b_33_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_33.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_33_mux_set(alsaqr_periph_padframe_periphs_b_33_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_33.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_33_mux_sel_t alsaqr_periph_padframe_periphs_b_33_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_34
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_34
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_34
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_34
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_34
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_34_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_34
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_34_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_34_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_34_group_ETH_port_ETH_TXD2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_34_group_GPIO_B_port_GPIO34 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_34_group_PWM1_port_PWM2 = 3,
} alsaqr_periph_padframe_periphs_b_34_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_34.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_34_mux_set(alsaqr_periph_padframe_periphs_b_34_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_34.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_34_mux_sel_t alsaqr_periph_padframe_periphs_b_34_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_35
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_35
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_35
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_35
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_35
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_35_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_35
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_35_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_35_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_35_group_ETH_port_ETH_TXD3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_35_group_GPIO_B_port_GPIO35 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_35_group_PWM1_port_PWM3 = 3,
} alsaqr_periph_padframe_periphs_b_35_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_35.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_35_mux_set(alsaqr_periph_padframe_periphs_b_35_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_35.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_35_mux_sel_t alsaqr_periph_padframe_periphs_b_35_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_36
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_36
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_36
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_36
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_36
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_36_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_36
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_36_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_36_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_36_group_CAM1_port_CAM_PCLK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_36_group_ETH_port_ETH_MDIO = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_36_group_GPIO_B_port_GPIO36 = 3,
} alsaqr_periph_padframe_periphs_b_36_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_36.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_36_mux_set(alsaqr_periph_padframe_periphs_b_36_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_36.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_36_mux_sel_t alsaqr_periph_padframe_periphs_b_36_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_37
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_37
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_37
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_37
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_37
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_37_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_37
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_37_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_37_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_37_group_CAM1_port_CAM_VSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_37_group_ETH_port_ETH_MDC = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_37_group_GPIO_B_port_GPIO37 = 3,
} alsaqr_periph_padframe_periphs_b_37_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_37.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_37_mux_set(alsaqr_periph_padframe_periphs_b_37_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_37.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_37_mux_sel_t alsaqr_periph_padframe_periphs_b_37_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_38
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_38
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_38
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_38
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_38
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_38_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_38
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_38_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_38_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_38_group_CAM1_port_CAM_HSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_38_group_GPIO_B_port_GPIO38 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_38_group_SPI10_port_SPI_SCK = 3,
} alsaqr_periph_padframe_periphs_b_38_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_38.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_38_mux_set(alsaqr_periph_padframe_periphs_b_38_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_38.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_38_mux_sel_t alsaqr_periph_padframe_periphs_b_38_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_39
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_39
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_39
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_39
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_39
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_39_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_39
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_39_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_39_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_39_group_CAM1_port_CAM_DATA0_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_39_group_GPIO_B_port_GPIO39 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_39_group_SPI10_port_SPI_CS0 = 3,
} alsaqr_periph_padframe_periphs_b_39_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_39.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_39_mux_set(alsaqr_periph_padframe_periphs_b_39_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_39.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_39_mux_sel_t alsaqr_periph_padframe_periphs_b_39_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_40
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_40
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_40
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_40
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_40
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_40_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_40
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_40_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_40_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_40_group_CAM1_port_CAM_DATA1_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_40_group_GPIO_B_port_GPIO40 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_40_group_SPI10_port_SPI_MISO = 3,
} alsaqr_periph_padframe_periphs_b_40_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_40.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_40_mux_set(alsaqr_periph_padframe_periphs_b_40_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_40.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_40_mux_sel_t alsaqr_periph_padframe_periphs_b_40_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_41
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_41
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_41
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_41
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_41
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_41_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_41
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_41_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_41_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_41_group_CAM1_port_CAM_DATA2_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_41_group_GPIO_B_port_GPIO41 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_41_group_SPI10_port_SPI_MOSI = 3,
} alsaqr_periph_padframe_periphs_b_41_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_41.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_41_mux_set(alsaqr_periph_padframe_periphs_b_41_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_41.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_41_mux_sel_t alsaqr_periph_padframe_periphs_b_41_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_42
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_42
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_42
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_42
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_42
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_42_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_42
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_42_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_42_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_42_group_CAM1_port_CAM_DATA3_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_42_group_CAN0_port_CAN_TX = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_42_group_GPIO_B_port_GPIO42 = 3,
} alsaqr_periph_padframe_periphs_b_42_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_42.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_42_mux_set(alsaqr_periph_padframe_periphs_b_42_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_42.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_42_mux_sel_t alsaqr_periph_padframe_periphs_b_42_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_43
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_43
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_43
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_43
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_43
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_43_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_43
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_43_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_43_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_43_group_CAM1_port_CAM_DATA4_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_43_group_CAN0_port_CAN_RX = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_43_group_GPIO_B_port_GPIO43 = 3,
} alsaqr_periph_padframe_periphs_b_43_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_43.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_43_mux_set(alsaqr_periph_padframe_periphs_b_43_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_43.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_43_mux_sel_t alsaqr_periph_padframe_periphs_b_43_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_44
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_44
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_44
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_44
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_44
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_44_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_44
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_44_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_44_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_44_group_CAM1_port_CAM_DATA5_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_44_group_GPIO_B_port_GPIO44 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_44_group_PWM1_port_PWM0 = 3,
} alsaqr_periph_padframe_periphs_b_44_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_44.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_44_mux_set(alsaqr_periph_padframe_periphs_b_44_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_44.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_44_mux_sel_t alsaqr_periph_padframe_periphs_b_44_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_45
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_45
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_45
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_45
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_45
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_45_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_45
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_45_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_45_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_45_group_CAM1_port_CAM_DATA6_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_45_group_GPIO_B_port_GPIO45 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_45_group_PWM1_port_PWM1 = 3,
} alsaqr_periph_padframe_periphs_b_45_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_45.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_45_mux_set(alsaqr_periph_padframe_periphs_b_45_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_45.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_45_mux_sel_t alsaqr_periph_padframe_periphs_b_45_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_46
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_46
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_46
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_46
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_46
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_46_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_46
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_46_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_46_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_46_group_CAM1_port_CAM_DATA7_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_46_group_GPIO_B_port_GPIO46 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_46_group_PWM1_port_PWM2 = 3,
} alsaqr_periph_padframe_periphs_b_46_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_46.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_46_mux_set(alsaqr_periph_padframe_periphs_b_46_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_46.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_46_mux_sel_t alsaqr_periph_padframe_periphs_b_46_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_47
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_47
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_47
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_47
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_47
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_47_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_47
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_47_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_group_FLL_CVA6_port_CLK_CVA6 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_group_GPIO_B_port_GPIO47 = 2,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_group_PWM1_port_PWM3 = 3,
} alsaqr_periph_padframe_periphs_b_47_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_47.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_47_mux_set(alsaqr_periph_padframe_periphs_b_47_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_47.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_47_mux_sel_t alsaqr_periph_padframe_periphs_b_47_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_spi_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_spi_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_spi_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_spi_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_spi_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_spi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_spi_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_00_group_SPI_OT_port_SPI_SCK = 1,
} alsaqr_periph_padframe_periphs_ot_spi_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_spi_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_spi_00_mux_set(alsaqr_periph_padframe_periphs_ot_spi_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_spi_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_spi_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_spi_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_spi_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_spi_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_spi_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_spi_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_spi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_spi_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_01_group_SPI_OT_port_SPI_CSN = 1,
} alsaqr_periph_padframe_periphs_ot_spi_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_spi_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_spi_01_mux_set(alsaqr_periph_padframe_periphs_ot_spi_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_spi_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_spi_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_01_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_spi_02
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_spi_02
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_spi_02
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_spi_02
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_spi_02
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_spi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_spi_02
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_02_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_02_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_02_group_SPI_OT_port_SPI_SD0 = 1,
} alsaqr_periph_padframe_periphs_ot_spi_02_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_spi_02.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_spi_02_mux_set(alsaqr_periph_padframe_periphs_ot_spi_02_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_spi_02.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_spi_02_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_02_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_spi_03
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_spi_03
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_spi_03
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_spi_03
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_spi_03
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_spi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_spi_03
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_spi_03_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_03_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_SPI_03_group_SPI_OT_port_SPI_SD1 = 1,
} alsaqr_periph_padframe_periphs_ot_spi_03_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_spi_03.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_spi_03_mux_set(alsaqr_periph_padframe_periphs_ot_spi_03_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_spi_03.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_spi_03_mux_sel_t alsaqr_periph_padframe_periphs_ot_spi_03_mux_get();




#endif /*  ALSAQR_PERIPH_PADFRAME_H */
