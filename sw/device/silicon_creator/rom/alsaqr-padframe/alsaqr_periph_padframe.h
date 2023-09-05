
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_00_group_I2C0_port_I2C_SCL = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_01_group_I2C0_port_I2C_SDA = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_02_group_SPI0_port_SPI_SCK = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_03_group_SPI0_port_SPI_CS0 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_04_group_SPI0_port_SPI_MISO = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_05_group_SPI0_port_SPI_MOSI = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_06_group_SPI1_port_SPI_SCK = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_07_group_SPI1_port_SPI_CS0 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_08_group_SPI1_port_SPI_MISO = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_09_group_SPI1_port_SPI_MOSI = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_10_group_SPI2_port_SPI_SCK = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_11_group_SPI2_port_SPI_CS0 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_12_group_SPI2_port_SPI_MISO = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_13_group_SPI2_port_SPI_MOSI = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_14_group_SPI3_port_SPI_SCK = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_15_group_SPI3_port_SPI_CS0 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_16_group_SPI3_port_SPI_MISO = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_17_group_SPI3_port_SPI_MOSI = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_18_group_SDIO0_port_SDIO_DATA0 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_19_group_SDIO0_port_SDIO_DATA1 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_20_group_SDIO0_port_SDIO_DATA2 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_21_group_SDIO0_port_SDIO_DATA3 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_22_group_SDIO0_port_SDIO_CLK = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_23_group_SDIO0_port_SDIO_CMD = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_24_group_UART0_port_UART_TX = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_25_group_UART0_port_UART_RX = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_26_group_I2C1_port_I2C_SCL = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_27_group_I2C1_port_I2C_SDA = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_28_group_USART0_port_UART_TX = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_29_group_USART0_port_UART_RX = 1,
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
 * Sets the chip2pad pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_30
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_30
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_30
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_30
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_30
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_30
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_30_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_30
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_30_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_30_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_30_group_USART0_port_UART_RTS = 1,
} alsaqr_periph_padframe_periphs_a_30_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_30.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_30_mux_set(alsaqr_periph_padframe_periphs_a_30_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_30.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_30_mux_sel_t alsaqr_periph_padframe_periphs_a_30_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_31
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_31
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_31
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_31
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_31
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_31
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_31_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_31
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_31_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_31_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_31_group_USART0_port_UART_CTS = 1,
} alsaqr_periph_padframe_periphs_a_31_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_31.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_31_mux_set(alsaqr_periph_padframe_periphs_a_31_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_31.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_31_mux_sel_t alsaqr_periph_padframe_periphs_a_31_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_32
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_32
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_32
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_32
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_32
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_32
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_32_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_32
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_32_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_32_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_32_group_SPI4_port_SPI_SCK = 1,
} alsaqr_periph_padframe_periphs_a_32_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_32.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_32_mux_set(alsaqr_periph_padframe_periphs_a_32_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_32.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_32_mux_sel_t alsaqr_periph_padframe_periphs_a_32_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_33
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_33
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_33
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_33
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_33
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_33
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_33_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_33
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_33_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_33_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_33_group_SPI4_port_SPI_CS0 = 1,
} alsaqr_periph_padframe_periphs_a_33_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_33.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_33_mux_set(alsaqr_periph_padframe_periphs_a_33_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_33.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_33_mux_sel_t alsaqr_periph_padframe_periphs_a_33_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_34
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_34
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_34
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_34
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_34
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_34
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_34_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_34
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_34_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_34_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_34_group_SPI4_port_SPI_MISO = 1,
} alsaqr_periph_padframe_periphs_a_34_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_34.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_34_mux_set(alsaqr_periph_padframe_periphs_a_34_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_34.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_34_mux_sel_t alsaqr_periph_padframe_periphs_a_34_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_35
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_35
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_35
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_35
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_35
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_35
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_35_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_35
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_35_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_35_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_35_group_SPI4_port_SPI_MOSI = 1,
} alsaqr_periph_padframe_periphs_a_35_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_35.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_35_mux_set(alsaqr_periph_padframe_periphs_a_35_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_35.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_35_mux_sel_t alsaqr_periph_padframe_periphs_a_35_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_36
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_36
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_36
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_36
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_36
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_36
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_36_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_36
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_36_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_36_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_36_group_I2C2_port_I2C_SCL = 1,
} alsaqr_periph_padframe_periphs_a_36_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_36.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_36_mux_set(alsaqr_periph_padframe_periphs_a_36_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_36.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_36_mux_sel_t alsaqr_periph_padframe_periphs_a_36_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_37
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_37
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_37
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_37
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_37
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_37
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_37_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_37
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_37_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_37_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_37_group_I2C2_port_I2C_SDA = 1,
} alsaqr_periph_padframe_periphs_a_37_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_37.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_37_mux_set(alsaqr_periph_padframe_periphs_a_37_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_37.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_37_mux_sel_t alsaqr_periph_padframe_periphs_a_37_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_38
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_38
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_38
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_38
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_38
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_38
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_38_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_38
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_38_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_38_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_38_group_PWM0_port_PWM0 = 1,
} alsaqr_periph_padframe_periphs_a_38_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_38.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_38_mux_set(alsaqr_periph_padframe_periphs_a_38_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_38.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_38_mux_sel_t alsaqr_periph_padframe_periphs_a_38_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_39
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_39
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_39
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_39
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_39
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_39
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_39_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_39
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_39_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_39_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_39_group_PWM0_port_PWM1 = 1,
} alsaqr_periph_padframe_periphs_a_39_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_39.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_39_mux_set(alsaqr_periph_padframe_periphs_a_39_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_39.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_39_mux_sel_t alsaqr_periph_padframe_periphs_a_39_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_40
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_40
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_40
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_40
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_40
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_40
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_40_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_40
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_40_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_40_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_40_group_PWM0_port_PWM2 = 1,
} alsaqr_periph_padframe_periphs_a_40_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_40.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_40_mux_set(alsaqr_periph_padframe_periphs_a_40_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_40.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_40_mux_sel_t alsaqr_periph_padframe_periphs_a_40_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_41
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_41
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_41
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_41
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_41
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_41
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_41_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_41
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_41_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_41_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_41_group_PWM0_port_PWM3 = 1,
} alsaqr_periph_padframe_periphs_a_41_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_41.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_41_mux_set(alsaqr_periph_padframe_periphs_a_41_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_41.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_41_mux_sel_t alsaqr_periph_padframe_periphs_a_41_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_42
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_42
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_42
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_42
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_42
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_42
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_42_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_42
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_42_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_42_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_42_group_CAM0_port_CAM_PCLK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_42_group_I2C3_port_I2C_SCL = 2,
} alsaqr_periph_padframe_periphs_a_42_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_42.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_42_mux_set(alsaqr_periph_padframe_periphs_a_42_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_42.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_42_mux_sel_t alsaqr_periph_padframe_periphs_a_42_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_43
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_43
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_43
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_43
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_43
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_43
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_43_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_43
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_43_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_43_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_43_group_CAM0_port_CAM_VSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_43_group_I2C3_port_I2C_SDA = 2,
} alsaqr_periph_padframe_periphs_a_43_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_43.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_43_mux_set(alsaqr_periph_padframe_periphs_a_43_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_43.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_43_mux_sel_t alsaqr_periph_padframe_periphs_a_43_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_44
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_44
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_44
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_44
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_44
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_44
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_44_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_44
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_44_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_44_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_44_group_CAM0_port_CAM_DATA0_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_44_group_SPI5_port_SPI_SCK = 2,
} alsaqr_periph_padframe_periphs_a_44_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_44.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_44_mux_set(alsaqr_periph_padframe_periphs_a_44_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_44.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_44_mux_sel_t alsaqr_periph_padframe_periphs_a_44_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_45
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_45
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_45
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_45
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_45
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_45
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_45_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_45
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_45_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_45_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_45_group_CAM0_port_CAM_DATA1_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_45_group_SPI5_port_SPI_CS0 = 2,
} alsaqr_periph_padframe_periphs_a_45_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_45.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_45_mux_set(alsaqr_periph_padframe_periphs_a_45_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_45.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_45_mux_sel_t alsaqr_periph_padframe_periphs_a_45_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_46
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_46
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_46
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_46
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_46
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_46
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_46_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_46
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_46_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_46_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_46_group_CAM0_port_CAM_DATA2_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_46_group_SPI5_port_SPI_MISO = 2,
} alsaqr_periph_padframe_periphs_a_46_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_46.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_46_mux_set(alsaqr_periph_padframe_periphs_a_46_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_46.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_46_mux_sel_t alsaqr_periph_padframe_periphs_a_46_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_47
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_47
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_47
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_47
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_47
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_47
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_47_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_47
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_47_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_47_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_47_group_CAM0_port_CAM_DATA3_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_47_group_SPI5_port_SPI_MOSI = 2,
} alsaqr_periph_padframe_periphs_a_47_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_47.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_47_mux_set(alsaqr_periph_padframe_periphs_a_47_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_47.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_47_mux_sel_t alsaqr_periph_padframe_periphs_a_47_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_48
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_48
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_48
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_48
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_48
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_48_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_48
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_48_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_48_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_48_group_CAM0_port_CAM_DATA5_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_48_group_SPI6_port_SPI_SCK = 2,
} alsaqr_periph_padframe_periphs_a_48_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_48.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_48_mux_set(alsaqr_periph_padframe_periphs_a_48_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_48.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_48_mux_sel_t alsaqr_periph_padframe_periphs_a_48_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_49
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_49
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_49
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_49
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_49
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_49_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_49
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_49_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_49_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_49_group_CAM0_port_CAM_DATA6_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_49_group_SPI6_port_SPI_CS0 = 2,
} alsaqr_periph_padframe_periphs_a_49_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_49.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_49_mux_set(alsaqr_periph_padframe_periphs_a_49_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_49.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_49_mux_sel_t alsaqr_periph_padframe_periphs_a_49_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_50
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_50
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_50
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_50
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_50
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_50_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_50
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_50_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_50_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_50_group_CAM0_port_CAM_DATA7_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_50_group_SPI6_port_SPI_MISO = 2,
} alsaqr_periph_padframe_periphs_a_50_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_50.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_50_mux_set(alsaqr_periph_padframe_periphs_a_50_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_50.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_50_mux_sel_t alsaqr_periph_padframe_periphs_a_50_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_51
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_51
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_51
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_51
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_51
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_51_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_51
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_51_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_51_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_51_group_CAM1_port_CAM_PCLK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_51_group_SPI6_port_SPI_MOSI = 2,
} alsaqr_periph_padframe_periphs_a_51_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_51.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_51_mux_set(alsaqr_periph_padframe_periphs_a_51_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_51.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_51_mux_sel_t alsaqr_periph_padframe_periphs_a_51_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_52
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_52
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_52
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_52
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_52
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_52_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_52
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_52_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_52_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_52_group_CAM1_port_CAM_HSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_52_group_SPI7_port_SPI_SCK = 2,
} alsaqr_periph_padframe_periphs_a_52_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_52.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_52_mux_set(alsaqr_periph_padframe_periphs_a_52_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_52.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_52_mux_sel_t alsaqr_periph_padframe_periphs_a_52_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_53
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_53
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_53
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_53
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_53
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_53_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_53
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_53_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_53_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_53_group_CAM1_port_CAM_DATA0_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_53_group_SPI7_port_SPI_MISO = 2,
} alsaqr_periph_padframe_periphs_a_53_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_53.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_53_mux_set(alsaqr_periph_padframe_periphs_a_53_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_53.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_53_mux_sel_t alsaqr_periph_padframe_periphs_a_53_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_54
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_54
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_54
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_54
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_54
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_54_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_54
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_54_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_54_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_54_group_CAM1_port_CAM_DATA1_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_54_group_SPI7_port_SPI_MOSI = 2,
} alsaqr_periph_padframe_periphs_a_54_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_54.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_54_mux_set(alsaqr_periph_padframe_periphs_a_54_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_54.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_54_mux_sel_t alsaqr_periph_padframe_periphs_a_54_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_55
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_55
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_55
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_55
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_55
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_55_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_55
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_55_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_55_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_55_group_CAM1_port_CAM_DATA5_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_55_group_SPI7_port_SPI_CS0 = 2,
} alsaqr_periph_padframe_periphs_a_55_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_55.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_55_mux_set(alsaqr_periph_padframe_periphs_a_55_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_55.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_55_mux_sel_t alsaqr_periph_padframe_periphs_a_55_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_56
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_56
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_56
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_56
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_56
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_56_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_56
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_56_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_56_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_56_group_CAM1_port_CAM_DATA6_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_56_group_SPI7_port_SPI_CS1 = 2,
} alsaqr_periph_padframe_periphs_a_56_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_56.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_56_mux_set(alsaqr_periph_padframe_periphs_a_56_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_56.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_56_mux_sel_t alsaqr_periph_padframe_periphs_a_56_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_57
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_57
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_57
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_57
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_57
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_57_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_57
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_57_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_57_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_57_group_CAM1_port_CAM_DATA7_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_57_group_I2C4_port_I2C_SCL = 2,
} alsaqr_periph_padframe_periphs_a_57_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_57.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_57_mux_set(alsaqr_periph_padframe_periphs_a_57_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_57.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_57_mux_sel_t alsaqr_periph_padframe_periphs_a_57_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_58
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_58
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_58
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_58
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_58
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_58_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_58
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_58_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_58_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_58_group_I2C4_port_I2C_SDA = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_58_group_SDIO1_port_SDIO_DATA0 = 2,
} alsaqr_periph_padframe_periphs_a_58_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_58.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_58_mux_set(alsaqr_periph_padframe_periphs_a_58_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_58.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_58_mux_sel_t alsaqr_periph_padframe_periphs_a_58_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_59
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_59
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_59
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_59
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_59
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_59_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_59
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_59_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_59_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_59_group_SDIO1_port_SDIO_DATA2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_59_group_UART1_port_UART_TX = 2,
} alsaqr_periph_padframe_periphs_a_59_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_59.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_59_mux_set(alsaqr_periph_padframe_periphs_a_59_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_59.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_59_mux_sel_t alsaqr_periph_padframe_periphs_a_59_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_60
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_60
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_60
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_60
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_60
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_60_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_60
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_60_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_60_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_60_group_SDIO1_port_SDIO_DATA3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_60_group_UART1_port_UART_RX = 2,
} alsaqr_periph_padframe_periphs_a_60_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_60.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_60_mux_set(alsaqr_periph_padframe_periphs_a_60_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_60.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_60_mux_sel_t alsaqr_periph_padframe_periphs_a_60_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_61
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_61
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_61
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_61
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_61
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_61_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_61
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_61_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_61_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_61_group_SDIO1_port_SDIO_CLK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_61_group_USART1_port_UART_TX = 2,
} alsaqr_periph_padframe_periphs_a_61_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_61.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_61_mux_set(alsaqr_periph_padframe_periphs_a_61_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_61.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_61_mux_sel_t alsaqr_periph_padframe_periphs_a_61_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_62
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_62
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_62
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_62
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_62
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_62_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_62
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_62_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_62_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_62_group_SDIO1_port_SDIO_CMD = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_62_group_USART1_port_UART_RX = 2,
} alsaqr_periph_padframe_periphs_a_62_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_62.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_62_mux_set(alsaqr_periph_padframe_periphs_a_62_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_62.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_62_mux_sel_t alsaqr_periph_padframe_periphs_a_62_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_63
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_63
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_63
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_63
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_63
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_63
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_63_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_63
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_63_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_63_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_63_group_USART1_port_UART_RTS = 1,
} alsaqr_periph_padframe_periphs_a_63_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_63.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_63_mux_set(alsaqr_periph_padframe_periphs_a_63_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_63.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_63_mux_sel_t alsaqr_periph_padframe_periphs_a_63_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_64
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_64
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_64
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_64
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_64
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_64
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_64_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_64
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_64_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_64_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_64_group_USART1_port_UART_CTS = 1,
} alsaqr_periph_padframe_periphs_a_64_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_64.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_64_mux_set(alsaqr_periph_padframe_periphs_a_64_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_64.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_64_mux_sel_t alsaqr_periph_padframe_periphs_a_64_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_65
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_65
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_65
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_65
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_65
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_65
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_65_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_65
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_65_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_65_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_65_group_UART2_port_UART_TX = 1,
} alsaqr_periph_padframe_periphs_a_65_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_65.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_65_mux_set(alsaqr_periph_padframe_periphs_a_65_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_65.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_65_mux_sel_t alsaqr_periph_padframe_periphs_a_65_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_66
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_66
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_66
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_66
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_66
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_66
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_66_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_66
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_66_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_66_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_66_group_UART2_port_UART_RX = 1,
} alsaqr_periph_padframe_periphs_a_66_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_66.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_66_mux_set(alsaqr_periph_padframe_periphs_a_66_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_66.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_66_mux_sel_t alsaqr_periph_padframe_periphs_a_66_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_67
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_67
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_67
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_67
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_67
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_67
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_67_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_67
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_67_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_67_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_67_group_I2C5_port_I2C_SCL = 1,
} alsaqr_periph_padframe_periphs_a_67_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_67.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_67_mux_set(alsaqr_periph_padframe_periphs_a_67_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_67.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_67_mux_sel_t alsaqr_periph_padframe_periphs_a_67_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_68
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_68
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_68
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_68
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_68
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_68
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_68_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_68
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_68_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_68_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_68_group_I2C5_port_I2C_SDA = 1,
} alsaqr_periph_padframe_periphs_a_68_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_68.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_68_mux_set(alsaqr_periph_padframe_periphs_a_68_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_68.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_68_mux_sel_t alsaqr_periph_padframe_periphs_a_68_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_69
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_69
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_69
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_69
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_69
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_69
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_69_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_69
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_69_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_69_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_69_group_USART2_port_UART_TX = 1,
} alsaqr_periph_padframe_periphs_a_69_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_69.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_69_mux_set(alsaqr_periph_padframe_periphs_a_69_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_69.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_69_mux_sel_t alsaqr_periph_padframe_periphs_a_69_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_70
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_70
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_70
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_70
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_70
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_70
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_70_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_70
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_70_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_70_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_70_group_USART2_port_UART_RX = 1,
} alsaqr_periph_padframe_periphs_a_70_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_70.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_70_mux_set(alsaqr_periph_padframe_periphs_a_70_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_70.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_70_mux_sel_t alsaqr_periph_padframe_periphs_a_70_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_71
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_71
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_71
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_71
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_71
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_71
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_71_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_71
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_71_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_71_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_71_group_USART2_port_UART_RTS = 1,
} alsaqr_periph_padframe_periphs_a_71_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_71.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_71_mux_set(alsaqr_periph_padframe_periphs_a_71_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_71.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_71_mux_sel_t alsaqr_periph_padframe_periphs_a_71_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_72
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_72
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_72
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_72
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_72
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_72
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_72_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_72
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_72_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_72_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_72_group_USART2_port_UART_CTS = 1,
} alsaqr_periph_padframe_periphs_a_72_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_72.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_72_mux_set(alsaqr_periph_padframe_periphs_a_72_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_72.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_72_mux_sel_t alsaqr_periph_padframe_periphs_a_72_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_73
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_73
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_73
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_73
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_73
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_73
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_73_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_73
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_73_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_73_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_73_group_USART3_port_UART_TX = 1,
} alsaqr_periph_padframe_periphs_a_73_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_73.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_73_mux_set(alsaqr_periph_padframe_periphs_a_73_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_73.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_73_mux_sel_t alsaqr_periph_padframe_periphs_a_73_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_74
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_74
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_74
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_74
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_74
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_74
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_74_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_74
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_74_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_74_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_74_group_USART3_port_UART_RX = 1,
} alsaqr_periph_padframe_periphs_a_74_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_74.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_74_mux_set(alsaqr_periph_padframe_periphs_a_74_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_74.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_74_mux_sel_t alsaqr_periph_padframe_periphs_a_74_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_75
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_75
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_75
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_75
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_75
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_75
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_75_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_75
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_75_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_75_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_75_group_USART3_port_UART_RTS = 1,
} alsaqr_periph_padframe_periphs_a_75_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_75.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_75_mux_set(alsaqr_periph_padframe_periphs_a_75_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_75.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_75_mux_sel_t alsaqr_periph_padframe_periphs_a_75_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_76
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_76
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_76
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_76
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_76
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_76
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_76_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_76
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_76_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_76_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_76_group_USART3_port_UART_CTS = 1,
} alsaqr_periph_padframe_periphs_a_76_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_76.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_76_mux_set(alsaqr_periph_padframe_periphs_a_76_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_76.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_76_mux_sel_t alsaqr_periph_padframe_periphs_a_76_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_77
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_77
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_77
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_77
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_77
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_77
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_77_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_77
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_77_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_77_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_77_group_PWM1_port_PWM0 = 1,
} alsaqr_periph_padframe_periphs_a_77_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_77.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_77_mux_set(alsaqr_periph_padframe_periphs_a_77_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_77.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_77_mux_sel_t alsaqr_periph_padframe_periphs_a_77_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_78
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_78
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_78
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_78
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_78
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_78
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_78_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_78
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_78_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_78_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_78_group_PWM1_port_PWM1 = 1,
} alsaqr_periph_padframe_periphs_a_78_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_78.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_78_mux_set(alsaqr_periph_padframe_periphs_a_78_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_78.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_78_mux_sel_t alsaqr_periph_padframe_periphs_a_78_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_79
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_79
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_79
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_79
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_79
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_79
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_79_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_79
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_79_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_79_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_79_group_PWM1_port_PWM2 = 1,
} alsaqr_periph_padframe_periphs_a_79_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_79.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_79_mux_set(alsaqr_periph_padframe_periphs_a_79_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_79.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_79_mux_sel_t alsaqr_periph_padframe_periphs_a_79_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_80
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_80
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_80
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_80
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_80
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_80
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_80_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_80
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_80_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_80_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_80_group_PWM1_port_PWM3 = 1,
} alsaqr_periph_padframe_periphs_a_80_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_80.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_80_mux_set(alsaqr_periph_padframe_periphs_a_80_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_80.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_80_mux_sel_t alsaqr_periph_padframe_periphs_a_80_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_81
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_81
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_81
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_81
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_81
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_81
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_81_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_81
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_81_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_81_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_81_group_CAN0_port_CAN_TX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_81_group_SPI8_port_SPI_SCK = 2,
} alsaqr_periph_padframe_periphs_a_81_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_81.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_81_mux_set(alsaqr_periph_padframe_periphs_a_81_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_81.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_81_mux_sel_t alsaqr_periph_padframe_periphs_a_81_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_82
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_82
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_82
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_82
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_82
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_82
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_82_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_82
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_82_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_82_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_82_group_CAN0_port_CAN_RX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_82_group_SPI8_port_SPI_CS0 = 2,
} alsaqr_periph_padframe_periphs_a_82_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_82.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_82_mux_set(alsaqr_periph_padframe_periphs_a_82_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_82.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_82_mux_sel_t alsaqr_periph_padframe_periphs_a_82_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_83
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_83
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_83
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_83
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_83
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_83
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_83_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_83
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_83_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_83_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_83_group_CAN1_port_CAN_TX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_83_group_SPI8_port_SPI_MISO = 2,
} alsaqr_periph_padframe_periphs_a_83_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_83.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_83_mux_set(alsaqr_periph_padframe_periphs_a_83_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_83.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_83_mux_sel_t alsaqr_periph_padframe_periphs_a_83_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_84
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_84
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_84
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_84
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_84
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_84
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_84_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_84
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_84_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_84_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_84_group_CAN1_port_CAN_RX = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_84_group_SPI8_port_SPI_MOSI = 2,
} alsaqr_periph_padframe_periphs_a_84_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_84.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_84_mux_set(alsaqr_periph_padframe_periphs_a_84_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_84.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_84_mux_sel_t alsaqr_periph_padframe_periphs_a_84_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_85
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_85
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_85
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_85
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_85
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_85
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_85_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_85
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_85_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_85_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_85_group_SPI9_port_SPI_SCK = 1,
} alsaqr_periph_padframe_periphs_a_85_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_85.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_85_mux_set(alsaqr_periph_padframe_periphs_a_85_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_85.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_85_mux_sel_t alsaqr_periph_padframe_periphs_a_85_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_86
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_86
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_86
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_86
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_86
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_86
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_86_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_86
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_86_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_86_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_86_group_SPI9_port_SPI_CS0 = 1,
} alsaqr_periph_padframe_periphs_a_86_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_86.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_86_mux_set(alsaqr_periph_padframe_periphs_a_86_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_86.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_86_mux_sel_t alsaqr_periph_padframe_periphs_a_86_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_87
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_87
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_87
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_87
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_87
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_87
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_87_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_87
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_87_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_87_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_87_group_SPI9_port_SPI_MISO = 1,
} alsaqr_periph_padframe_periphs_a_87_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_87.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_87_mux_set(alsaqr_periph_padframe_periphs_a_87_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_87.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_87_mux_sel_t alsaqr_periph_padframe_periphs_a_87_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_88
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_88
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_88
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_88
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_88
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_88
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_88_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_88
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_88_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_88_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_88_group_SPI9_port_SPI_MOSI = 1,
} alsaqr_periph_padframe_periphs_a_88_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_88.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_88_mux_set(alsaqr_periph_padframe_periphs_a_88_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_88.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_88_mux_sel_t alsaqr_periph_padframe_periphs_a_88_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_89
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_89
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_89
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_89
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_89
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_89
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_89_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_89
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_89_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_89_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_89_group_SPI10_port_SPI_SCK = 1,
} alsaqr_periph_padframe_periphs_a_89_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_89.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_89_mux_set(alsaqr_periph_padframe_periphs_a_89_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_89.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_89_mux_sel_t alsaqr_periph_padframe_periphs_a_89_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_90
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_90
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_90
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_90
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_90
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_90
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_90_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_90
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_90_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_90_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_90_group_SPI10_port_SPI_CS0 = 1,
} alsaqr_periph_padframe_periphs_a_90_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_90.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_90_mux_set(alsaqr_periph_padframe_periphs_a_90_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_90.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_90_mux_sel_t alsaqr_periph_padframe_periphs_a_90_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_91
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_91
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_91
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_91
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_91
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_91
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_91_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_91
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_91_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_91_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_91_group_SPI10_port_SPI_MISO = 1,
} alsaqr_periph_padframe_periphs_a_91_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_91.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_91_mux_set(alsaqr_periph_padframe_periphs_a_91_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_91.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_91_mux_sel_t alsaqr_periph_padframe_periphs_a_91_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: a_92
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: a_92
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: a_92
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: a_92
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: a_92
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: a_92
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_a_92_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: a_92
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_a_92_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_92_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_A_92_group_SPI10_port_SPI_MOSI = 1,
} alsaqr_periph_padframe_periphs_a_92_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls a_92.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_a_92_mux_set(alsaqr_periph_padframe_periphs_a_92_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for a_92.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_a_92_mux_sel_t alsaqr_periph_padframe_periphs_a_92_mux_get();



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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_CAM0_port_CAM_HSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_19_group_GPIO_B_port_GPIO19 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_CAM0_port_CAM_DATA4_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_20_group_GPIO_B_port_GPIO20 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_CAM1_port_CAM_VSYNC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_21_group_GPIO_B_port_GPIO21 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_CAM1_port_CAM_DATA2_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_22_group_GPIO_B_port_GPIO22 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_CAM1_port_CAM_DATA3_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_23_group_GPIO_B_port_GPIO23 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_CAM1_port_CAM_DATA4_I = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_24_group_GPIO_B_port_GPIO24 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_GPIO_B_port_GPIO25 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_25_group_SDIO1_port_SDIO_DATA1 = 2,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_26_group_GPIO_B_port_GPIO26 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_27_group_GPIO_B_port_GPIO27 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_28_group_GPIO_B_port_GPIO28 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_29_group_GPIO_B_port_GPIO29 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_30_group_GPIO_B_port_GPIO30 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_31_group_GPIO_B_port_GPIO31 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_32_group_GPIO_B_port_GPIO32 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_33_group_GPIO_B_port_GPIO33 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_34_group_GPIO_B_port_GPIO34 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_35_group_GPIO_B_port_GPIO35 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_36_group_GPIO_B_port_GPIO36 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_37_group_GPIO_B_port_GPIO37 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_38_group_GPIO_B_port_GPIO38 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_39_group_GPIO_B_port_GPIO39 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_40_group_GPIO_B_port_GPIO40 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_41_group_GPIO_B_port_GPIO41 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_42_group_GPIO_B_port_GPIO42 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_43_group_GPIO_B_port_GPIO43 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_44_group_GPIO_B_port_GPIO44 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_45_group_GPIO_B_port_GPIO45 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_46_group_GPIO_B_port_GPIO46 = 1,
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
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_group_ETH_port_ETH_RST = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_47_group_GPIO_B_port_GPIO47 = 2,
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
 * Sets the chip2pad pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_48
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_48
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_48
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_48
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_48
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_48
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_48_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_48
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_48_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_48_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_48_group_ETH_port_ETH_RXCK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_48_group_GPIO_B_port_GPIO48 = 2,
} alsaqr_periph_padframe_periphs_b_48_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_48.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_48_mux_set(alsaqr_periph_padframe_periphs_b_48_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_48.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_48_mux_sel_t alsaqr_periph_padframe_periphs_b_48_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_49
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_49
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_49
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_49
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_49
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_49
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_49_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_49
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_49_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_49_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_49_group_ETH_port_ETH_RXCTL = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_49_group_GPIO_B_port_GPIO49 = 2,
} alsaqr_periph_padframe_periphs_b_49_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_49.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_49_mux_set(alsaqr_periph_padframe_periphs_b_49_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_49.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_49_mux_sel_t alsaqr_periph_padframe_periphs_b_49_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_50
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_50
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_50
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_50
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_50
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_50
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_50_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_50
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_50_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_50_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_50_group_ETH_port_ETH_RXD0 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_50_group_GPIO_B_port_GPIO50 = 2,
} alsaqr_periph_padframe_periphs_b_50_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_50.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_50_mux_set(alsaqr_periph_padframe_periphs_b_50_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_50.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_50_mux_sel_t alsaqr_periph_padframe_periphs_b_50_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_51
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_51
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_51
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_51
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_51
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_51
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_51_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_51
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_51_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_51_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_51_group_ETH_port_ETH_RXD1 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_51_group_GPIO_B_port_GPIO51 = 2,
} alsaqr_periph_padframe_periphs_b_51_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_51.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_51_mux_set(alsaqr_periph_padframe_periphs_b_51_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_51.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_51_mux_sel_t alsaqr_periph_padframe_periphs_b_51_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_52
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_52
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_52
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_52
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_52
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_52
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_52_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_52
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_52_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_52_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_52_group_ETH_port_ETH_RXD2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_52_group_GPIO_B_port_GPIO52 = 2,
} alsaqr_periph_padframe_periphs_b_52_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_52.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_52_mux_set(alsaqr_periph_padframe_periphs_b_52_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_52.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_52_mux_sel_t alsaqr_periph_padframe_periphs_b_52_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_53
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_53
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_53
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_53
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_53
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_53
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_53_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_53
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_53_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_53_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_53_group_ETH_port_ETH_RXD3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_53_group_GPIO_B_port_GPIO53 = 2,
} alsaqr_periph_padframe_periphs_b_53_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_53.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_53_mux_set(alsaqr_periph_padframe_periphs_b_53_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_53.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_53_mux_sel_t alsaqr_periph_padframe_periphs_b_53_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_54
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_54
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_54
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_54
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_54
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_54
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_54_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_54
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_54_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_54_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_54_group_ETH_port_ETH_TXCK = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_54_group_GPIO_B_port_GPIO54 = 2,
} alsaqr_periph_padframe_periphs_b_54_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_54.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_54_mux_set(alsaqr_periph_padframe_periphs_b_54_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_54.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_54_mux_sel_t alsaqr_periph_padframe_periphs_b_54_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_55
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_55
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_55
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_55
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_55
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_55
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_55_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_55
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_55_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_55_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_55_group_ETH_port_ETH_TXCTL = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_55_group_GPIO_B_port_GPIO55 = 2,
} alsaqr_periph_padframe_periphs_b_55_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_55.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_55_mux_set(alsaqr_periph_padframe_periphs_b_55_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_55.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_55_mux_sel_t alsaqr_periph_padframe_periphs_b_55_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_56
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_56
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_56
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_56
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_56
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_56
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_56_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_56
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_56_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_56_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_56_group_ETH_port_ETH_TXD0 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_56_group_GPIO_B_port_GPIO56 = 2,
} alsaqr_periph_padframe_periphs_b_56_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_56.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_56_mux_set(alsaqr_periph_padframe_periphs_b_56_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_56.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_56_mux_sel_t alsaqr_periph_padframe_periphs_b_56_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_57
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_57
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_57
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_57
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_57
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_57
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_57_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_57
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_57_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_57_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_57_group_ETH_port_ETH_TXD1 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_57_group_GPIO_B_port_GPIO57 = 2,
} alsaqr_periph_padframe_periphs_b_57_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_57.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_57_mux_set(alsaqr_periph_padframe_periphs_b_57_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_57.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_57_mux_sel_t alsaqr_periph_padframe_periphs_b_57_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_58
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_58
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_58
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_58
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_58
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_58
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_58_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_58
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_58_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_58_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_58_group_ETH_port_ETH_TXD2 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_58_group_GPIO_B_port_GPIO58 = 2,
} alsaqr_periph_padframe_periphs_b_58_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_58.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_58_mux_set(alsaqr_periph_padframe_periphs_b_58_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_58.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_58_mux_sel_t alsaqr_periph_padframe_periphs_b_58_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_59
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_59
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_59
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_59
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_59
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_59
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_59_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_59
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_59_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_59_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_59_group_ETH_port_ETH_TXD3 = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_59_group_GPIO_B_port_GPIO59 = 2,
} alsaqr_periph_padframe_periphs_b_59_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_59.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_59_mux_set(alsaqr_periph_padframe_periphs_b_59_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_59.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_59_mux_sel_t alsaqr_periph_padframe_periphs_b_59_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_60
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_60
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_60
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_60
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_60
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_60
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_60_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_60
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_60_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_60_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_60_group_ETH_port_ETH_MDIO = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_60_group_GPIO_B_port_GPIO60 = 2,
} alsaqr_periph_padframe_periphs_b_60_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_60.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_60_mux_set(alsaqr_periph_padframe_periphs_b_60_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_60.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_60_mux_sel_t alsaqr_periph_padframe_periphs_b_60_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_61
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_61
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_61
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_61
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_61
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_61
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_61_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_61
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_61_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_61_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_61_group_ETH_port_ETH_MDC = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_61_group_GPIO_B_port_GPIO61 = 2,
} alsaqr_periph_padframe_periphs_b_61_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_61.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_61_mux_set(alsaqr_periph_padframe_periphs_b_61_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_61.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_61_mux_sel_t alsaqr_periph_padframe_periphs_b_61_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: b_62
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: b_62
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: b_62
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: b_62
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: b_62
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: b_62
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_b_62_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: b_62
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_b_62_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_62_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_62_group_ETH_port_ETH_INTB = 1,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_B_62_group_GPIO_B_port_GPIO62 = 2,
} alsaqr_periph_padframe_periphs_b_62_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls b_62.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_b_62_mux_set(alsaqr_periph_padframe_periphs_b_62_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for b_62.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_b_62_mux_sel_t alsaqr_periph_padframe_periphs_b_62_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_00_group_QSPI_OT_port_QSPI_SCK = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_00_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_01_group_QSPI_OT_port_QSPI_CSN = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_01_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_01_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_02
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_02
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_02
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_02
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_02
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_02
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_02_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_02_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_02_group_QSPI_OT_port_QSPI_SD0 = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_02_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_02.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_02_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_02_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_02.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_02_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_02_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_03
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_03
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_03
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_03
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_03
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_03
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_03_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_03_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_03_group_QSPI_OT_port_QSPI_SD1 = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_03_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_03.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_03_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_03_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_03.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_03_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_03_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_04
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_04
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_04
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_04
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_04
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_04
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_04_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_04_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_04_group_QSPI_OT_port_QSPI_SD2 = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_04_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_04.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_04_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_04_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_04.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_04_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_04_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_qspi_05
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_qspi_05
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_qspi_05
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_qspi_05
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_qspi_05
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_qspi_05
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_qspi_05_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_05_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_QSPI_05_group_QSPI_OT_port_QSPI_SD3 = 1,
} alsaqr_periph_padframe_periphs_ot_qspi_05_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_qspi_05.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_qspi_05_mux_set(alsaqr_periph_padframe_periphs_ot_qspi_05_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_qspi_05.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_qspi_05_mux_sel_t alsaqr_periph_padframe_periphs_ot_qspi_05_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_00_group_QSPI_LINUX_port_QSPI_SCK = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_00_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_00_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_01_group_QSPI_LINUX_port_QSPI_CSN = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_01_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_01_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_01_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_02
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_02
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_02
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_02
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_02
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_02
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_02
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_02_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_02_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_02_group_QSPI_LINUX_port_QSPI_SD0 = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_02_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_02.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_02_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_02_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_02.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_02_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_02_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_03
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_03
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_03
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_03
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_03
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_03
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_03
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_03_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_03_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_03_group_QSPI_LINUX_port_QSPI_SD1 = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_03_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_03.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_03_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_03_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_03.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_03_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_03_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_04
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_04
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_04
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_04
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_04
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_04
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_04
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_04_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_04_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_04_group_QSPI_LINUX_port_QSPI_SD2 = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_04_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_04.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_04_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_04_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_04.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_04_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_04_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: linux_qspi_05
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: linux_qspi_05
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: linux_qspi_05
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: linux_qspi_05
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: linux_qspi_05
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: linux_qspi_05
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: linux_qspi_05
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_linux_qspi_05_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_05_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_LINUX_QSPI_05_group_QSPI_LINUX_port_QSPI_SD3 = 1,
} alsaqr_periph_padframe_periphs_linux_qspi_05_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls linux_qspi_05.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_linux_qspi_05_mux_set(alsaqr_periph_padframe_periphs_linux_qspi_05_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for linux_qspi_05.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_linux_qspi_05_mux_sel_t alsaqr_periph_padframe_periphs_linux_qspi_05_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_gpio_00
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_gpio_00
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_gpio_00
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_gpio_00
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_gpio_00
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_gpio_00
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_gpio_00
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_00_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_GPIO_00_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_GPIO_00_group_OT_GPIO_port_OP_GPIO0 = 1,
} alsaqr_periph_padframe_periphs_ot_gpio_00_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_gpio_00.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_00_mux_set(alsaqr_periph_padframe_periphs_ot_gpio_00_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_gpio_00.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_gpio_00_mux_sel_t alsaqr_periph_padframe_periphs_ot_gpio_00_mux_get();



/**
 * Sets the chip2pad pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_chip2pad_set(uint8_t value);

/**
 * Get the currently configured chip2pad value for the pad: ot_gpio_01
 *
 * @return The value of the chip2pad field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_chip2pad_get();

/**
 * Sets the drv pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 3.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_drv_set(uint8_t value);

/**
 * Get the currently configured drv value for the pad: ot_gpio_01
 *
 * @return The value of the drv field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_drv_get();

/**
 * Sets the oen pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_oen_set(uint8_t value);

/**
 * Get the currently configured oen value for the pad: ot_gpio_01
 *
 * @return The value of the oen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_oen_get();

/**
 * Sets the puen pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_puen_set(uint8_t value);

/**
 * Get the currently configured puen value for the pad: ot_gpio_01
 *
 * @return The value of the puen field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_puen_get();

/**
 * Sets the slw pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_slw_set(uint8_t value);

/**
 * Get the currently configured slw value for the pad: ot_gpio_01
 *
 * @return The value of the slw field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_slw_get();

/**
 * Sets the smt pad signal for the pad: ot_gpio_01
 *
 * @param value The value to program into the pad configuration register. A value smaller than 1.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_smt_set(uint8_t value);

/**
 * Get the currently configured smt value for the pad: ot_gpio_01
 *
 * @return The value of the smt field
 */
uint8_t alsaqr_periph_padframe_periphs_ot_gpio_01_cfg_smt_get();

typedef enum {
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_GPIO_01_REGISTER = 0,
  ALSAQR_PERIPH_PADFRAME_PERIPHS_OT_GPIO_01_group_OT_GPIO_port_OP_GPIO1 = 1,
} alsaqr_periph_padframe_periphs_ot_gpio_01_mux_sel_t;

/**
   * Choose the entity (a port or the dedicated configuration register) that controls ot_gpio_01.
   *
   * @param mux_sel Port or configuration register to connect to the pad.
 */
void alsaqr_periph_padframe_periphs_ot_gpio_01_mux_set(alsaqr_periph_padframe_periphs_ot_gpio_01_mux_sel_t mux_sel);

/**
 * Read the current multiplexer select value configured for ot_gpio_01.
 *
 * @return Port or configuration register currently connected to the pad.
 */
 alsaqr_periph_padframe_periphs_ot_gpio_01_mux_sel_t alsaqr_periph_padframe_periphs_ot_gpio_01_mux_get();




#endif /*  ALSAQR_PERIPH_PADFRAME_H */
