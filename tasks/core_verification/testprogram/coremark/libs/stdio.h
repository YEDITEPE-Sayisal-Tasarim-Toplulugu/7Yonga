#ifndef __STDIO_H__
#define __STDIO_H__

#include <stdint.h>

void printf_init(void (*_putc)(char), int (*_readc)(void));

int sprintf(char *buf, const char *fmt, ...);
void printf(const char *fmt, ...);

int scanf(const char* format, ...);

#endif