// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "utils.h"

/*
unsigned int get_mepc() {
  uint32_t result;
  __asm__ volatile("csrr %0, mepc;" : "=r"(result));
  return result;
}

unsigned int get_mcause() {
  uint32_t result;
  __asm__ volatile("csrr %0, mcause;" : "=r"(result));
  return result;
}

unsigned int get_mtval() {
  uint32_t result;
  __asm__ volatile("csrr %0, mtval;" : "=r"(result));
  return result;
  }*/


void simple_exc_handler(void) {
  printf("EXCEPTION!!!\r\n");
  /*
  rputs("============\n");
  puts("MEPC:   0x");
  puthex(get_mepc());
  puts("\nMCAUSE: 0x");
  puthex(get_mcause());
  puts("\nMTVAL:  0x");
  puthex(get_mtval());
  putchar('\n');
  */
}


void uart_set_cfg(int parity, uint16_t clk_counter) {
  unsigned int i;
  *(volatile unsigned int*)(UART_REG_LCR) = 0x83; //sets 8N1 and set DLAB to 1
  *(volatile unsigned int*)(UART_REG_DLM) = (clk_counter >> 8) & 0xFF;
  *(volatile unsigned int*)(UART_REG_DLL) =  clk_counter       & 0xFF;
  *(volatile unsigned int*)(UART_REG_FCR) = 0xA7; //enables 16byte FIFO and clear FIFOs
  *(volatile unsigned int*)(UART_REG_LCR) = 0x03; //sets 8N1 and set DLAB to 0

  *(volatile unsigned int*)(UART_REG_IER) = ((*(volatile unsigned int*)(UART_REG_IER)) & 0xF0) | 0x02; // set IER (interrupt enable register) on UART
}

void uart_send(const char* str, unsigned int len) {
  unsigned int i;

  while(len > 0) {
    // process this in batches of 16 bytes to actually use the FIFO in the UART

    // wait until there is space in the fifo
    while( (*(volatile unsigned int*)(UART_REG_LSR) & 0x20) == 0);

    for(i = 0; (i < UART_FIFO_DEPTH) && (len > 0); i++) {
      // load FIFO
      *(volatile unsigned int*)(UART_REG_THR) = *str++;

      len--;
    }
  }
}

char uart_getchar() {
  while((*((volatile int*)UART_REG_LSR) & 0x1) != 0x1);

  return *(volatile int*)UART_REG_RBR;
}

void uart_sendchar(const char c) {
  // wait until there is space in the fifo
  while( (*(volatile unsigned int*)(UART_REG_LSR) & 0x20) == 0);

  // load FIFO
  *(volatile unsigned int*)(UART_REG_THR) = c;
}

void uart_wait_tx_done(void) {
  // wait until there is space in the fifo
  while( (*(volatile unsigned int*)(UART_REG_LSR) & 0x40) == 0);
}


#define PAD_RIGHT 1
#define PAD_ZERO  2

/* the following should be enough for 32 bit int */
#define PRINT_BUF_LEN 32

/* define LONG_MAX for int32 */
#define LONG_MAX 2147483647L

/* DETECTNULL returns nonzero if (long)X contains a NULL byte. */
#if LONG_MAX == 2147483647L
#define DETECTNULL(X) (((X) - 0x01010101) & ~(X) & 0x80808080)
#else
#if LONG_MAX == 9223372036854775807L
#define DETECTNULL(X) (((X) - 0x0101010101010101) & ~(X) & 0x8080808080808080)
#else
#error long int is not a 32bit or 64bit type.
#endif
#endif

/* Nonzero if either X or Y is not aligned on a "long" boundary. */
#define UNALIGNED(X, Y) \
  (((long)X & (sizeof (long) - 1)) | ((long)Y & (sizeof (long) - 1)))

static unsigned divu10(unsigned n) {
  unsigned q, r;

  q = (n >> 1) + (n >> 2);
  q = q + (q >> 4);
  q = q + (q >> 8);
  q = q + (q >> 16);
  q = q >> 3;
  r = n - q * 10;

  return q + ((r + 6) >> 4);
}

char remu10_table[16] = {
  0, 1, 2, 2, 3, 3, 4, 5,
  5, 6, 7, 7, 8, 8, 9, 0
};

static unsigned remu10(unsigned n) {
  n = (0x19999999 * n + (n >> 1) + (n >> 3)) >> 28;
  return remu10_table[n];
}

int putchar(int s)
{
  uart_sendchar(s);
  return s;
}

static void qprintchar(char **str, int c)
{
  if (str)
  {
    **str = c;
    ++(*str);
  }
  else
    putchar((char)c);
}

static int qprints(char **out, const char *string, int width, int pad)
{
  register int pc = 0, padchar = ' ';

  if (width > 0) {
    register int len = 0;
    register const char *ptr;
    for (ptr = string; *ptr; ++ptr) ++len;
    if (len >= width) width = 0;
    else width -= len;
    if (pad & PAD_ZERO) padchar = '0';
  }
  if (!(pad & PAD_RIGHT)) {
    for ( ; width > 0; --width) {
      qprintchar (out, padchar);
      ++pc;
    }
  }
  for ( ; *string ; ++string) {
    qprintchar (out, *string);
    ++pc;
  }
  for ( ; width > 0; --width) {
    qprintchar (out, padchar);
    ++pc;
  }

  return pc;
}

static int qprinti(char **out, int i, int b, int sg, int width, int pad, char letbase)
{
  char print_buf[PRINT_BUF_LEN];
  register char *s;
  register int neg = 0, pc = 0;
  unsigned int t,u = i;

  if (i == 0)
  {
    print_buf[0] = '0';
    print_buf[1] = '\0';
    return qprints (out, print_buf, width, pad);
  }

  if (sg && b == 10 && i < 0)
  {
    neg = 1;
    u = -i;
  }

  s = print_buf + PRINT_BUF_LEN-1;
  *s = '\0';

  // treat HEX and decimal differently
  if(b == 16) {
    // HEX
    while (u) {
      int t = u & 0xF;

      if (t >= 10)
        t += letbase - '0' - 10;

      *--s = t + '0';
      u >>= 4;
    }
  } else {
    // decimal
    while (u) {
      *--s = remu10(u) + '0';
      u = divu10(u);
    }
  }

  if (neg) {
    if( width && (pad & PAD_ZERO) )
    {
      qprintchar (out, '-');
      ++pc;
      --width;
    }
    else
    {
      *--s = '-';
    }
  }
  return pc + qprints (out, s, width, pad);
}

static int qprint(char **out, const char *format, va_list va)
{
  register int width, pad;
  register int pc = 0;
  char scr[2];

  for (; *format != 0; ++format)
  {
    if (*format == '%')
    {
      ++format;
      width = pad = 0;
      if (*format == '\0') break;
      if (*format == '%') goto out;
      if (*format == '-')
      {
        ++format;
        pad = PAD_RIGHT;
      }
      while (*format == '0')
      {
        ++format;
        pad |= PAD_ZERO;
      }
      for ( ; *format >= '0' && *format <= '9'; ++format) {
        width *= 10;
        width += *format - '0';
      }
      if( *format == 's' ) {
        register char *s = va_arg(va, char*);
        pc += qprints (out, s?s:"(null)", width, pad);
        continue;
      }
      if( *format == 'd' ) {
        pc += qprinti (out, va_arg(va, int), 10, 1, width, pad, 'a');
        continue;
      }
      if( *format == 'u' ) {
        pc += qprinti (out, va_arg(va, unsigned int), 10, 0, width, pad, 'a');
        continue;
      }
      if( *format == 'x' ) {
        pc += qprinti (out, va_arg(va, uint32_t), 16, 0, width, pad, 'a');
        continue;
      }
      if( *format == 'X' ) {
        pc += qprinti (out, va_arg(va, uint32_t), 16, 0, width, pad, 'A');
        continue;
      }
      if( *format == 'c' ) {
        scr[0] = va_arg(va, int);
        scr[1] = '\0';
        pc += qprints (out, scr, width, pad);
        continue;
      }
    }
    else
    {
out:
      qprintchar (out, *format);
      ++pc;
    }
  }
  if (out) **out = '\0';

  return pc;
}

int printf(const char *format, ...)
{
  int pc;
  va_list va;

  va_start(va, format);

  pc = qprint(0, format, va);

  va_end(va);

  return pc;

}

int puts(const char *s)
{
  int i=0;

  while(s[i] != '\0')
    putchar(s[i++]);

  putchar('\n');

  return i;
}

__attribute__ ((weak)) void external_irq_handler(void) {
   return;
}
