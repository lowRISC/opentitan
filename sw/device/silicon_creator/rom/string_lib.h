// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the ?License?); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an ?AS IS? BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

#ifndef STRING_LIB_H
#define STRING_LIB_H

#include <stddef.h>

// putchar is defined as a macro which gets in the way of our prototype below
#ifdef putchar
#undef putchar
#endif

size_t strlen (const char *str);
int  strcmp (const char *s1, const char *s2);
char* strcpy (char *s1, const char *s2);
int puts(const char *s);
int printf(const char *format, ...);
void * memset (void *dest, int val, size_t len);
int putchar(int s);

#endif
