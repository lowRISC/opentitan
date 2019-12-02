#ifndef _F_LIB_OLED_DRIVER_H__
#define _F_LIB_OLED_DRIVER_H__

#include <stddef.h>
#include <stdint.h>

#define OLED_ROWS 4
#define OLED_BYTE_COLS 128
#define OLED_WORD_COLS 32

int oled_on_ready();
int oled_off_ready();
void oled_on();
void oled_off();
void oled_write_disp();
void oled_write_pixbuf_word(uint32_t row, uint32_t word_col, uint32_t pix_word);
void oled_write_pixbuf_byte(uint32_t row, uint32_t byte_col, uint8_t pix_byte);
void oled_clear(uint32_t clear_black);
void oled_write_image(uint32_t img[]);
#ifdef OLED_DRIVER_INC_FONT
void oled_write_char(char c, uint32_t row, uint32_t word_col);
void oled_write_str(const char* str, uint32_t row, uint32_t word_col);
#endif

#endif

