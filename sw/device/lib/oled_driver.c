#include "sw/device/lib/common.h"
#include "oled_driver_regs.h"
#include "oled_driver.h"
#ifdef OLED_DRIVER_INC_FONT
#include "oled_font.h"
#endif

#include <stdint.h>

#define OLED_DRIVER0_BASE_ADDR 0x40150000

int oled_on_ready() {
  return REG32(OLED_DRIVER_STATUS(0)) & (1 << OLED_DRIVER_STATUS_ON_READY);
}

int oled_off_ready() {
  return REG32(OLED_DRIVER_STATUS(0)) & (1 << OLED_DRIVER_STATUS_OFF_READY);
}

void oled_on() {
  while(!oled_on_ready());

  REG32(OLED_DRIVER_CMD(0)) = (1 << OLED_DRIVER_CMD_DISP_ON);
}

void oled_off() {
  while(!oled_off_ready());

  REG32(OLED_DRIVER_CMD(0)) = (1 << OLED_DRIVER_CMD_DISP_OFF);
}

void oled_write_disp() {
  while(!(REG32(OLED_DRIVER_STATUS(0)) & (1 << OLED_DRIVER_STATUS_DISP_READY)));

  REG32(OLED_DRIVER_CMD(0)) = (1 << OLED_DRIVER_CMD_DISP_WRITE);
}

void oled_write_pixbuf_word(uint32_t row, uint32_t word_col, uint32_t pix_word) {
  volatile uint32_t* oled_pix_buf = (volatile uint32_t* )OLED_DRIVER_PIX_BUF(0);

  oled_pix_buf += (row * OLED_WORD_COLS) + word_col;

  *oled_pix_buf = pix_word;
}

void old_write_pixbuf_byte(uint32_t row, uint32_t byte_col, uint8_t pix_byte) {
  volatile uint8_t* oled_pix_buf = (volatile uint8_t* )OLED_DRIVER_PIX_BUF(0);

  oled_pix_buf += (row * OLED_BYTE_COLS) + byte_col;

  *oled_pix_buf = pix_byte;
}

void oled_clear(uint32_t clear_black) {
  uint32_t clear_word = clear_black ? 0 : 0xFFFFFFFF;

  for (uint32_t row = 0;row < OLED_ROWS; ++row) {
    for (uint32_t col = 0;col < OLED_WORD_COLS; ++col) {
      oled_write_pixbuf_word(row, col, clear_word);
    }
  }

  oled_write_disp();
}

void oled_write_image(uint32_t img[]) {
  volatile uint32_t* oled_pix_buf = (volatile uint32_t* )OLED_DRIVER_PIX_BUF(0);

  for(uint32_t i = 0;i < OLED_ROWS * OLED_WORD_COLS; ++i) {
    *oled_pix_buf++ = img[i];
  }
}

#ifdef OLED_DRIVER_INC_FONT
void oled_write_char(char c, uint32_t row, uint32_t word_col) {
  uint32_t* char_bitmap = &oled_font[(uint32_t)c * 4];

  for(uint32_t char_col = 0; char_col < 2; ++char_col) {
    for(uint32_t char_row = 0; char_row < 2; ++char_row) {
      oled_write_pixbuf_word(char_row + row, char_col + word_col, char_bitmap[char_row * 2 + char_col]);
    }
  }
}

void oled_write_str(const char* str, uint32_t row, uint32_t word_col) {
  if(row > (OLED_ROWS - 2)) {
    return;
  }

  while(*str) {
    if(word_col > (OLED_WORD_COLS - 2)) {
      return;
    }

    oled_write_char(*str, row, word_col);
    ++str;
    word_col += 2;
  }
}
#endif

