#ifndef __STRING_H__
#define __STRING_H__

#include <stdint.h>

typedef uint32_t size_t;

int tolower(int ch);
int toupper(int ch);

size_t strlen(const char * str);
size_t strnlen(char * str, size_t n);

int strcmp(char* s1, char* s2);
int strncmp(char * s1, char * s2, size_t n);
int strcasecmp(char* s1, char* s2);
int strncasecmp(char * s1, char * s2, size_t n);

char *strcat(char *dst, char *src);
char *strncat(char *s1, char *s2, size_t count);

char * strcpy(char * dst, char * src);
char * strncpy(char * dst, char * src, size_t n);

char * strrchr(char *cp, int ch);
char *strchr(char *s, int c);

void reverse(char s[]);
void reverse_wlen(char* str, int len);

int itoa(int num, unsigned char* str, int len, int base);
int atoi(const char *str);
int atoi_hex(const char *str);
void hexToStrDigits(unsigned int num, char* str, int numDigits);

// MEM COMMANDS
void *memset(void *p, int c, size_t n);
void *memmove(void *v_dst, const void *v_src, size_t length);
void *memcpy(void *dst, const void *src, size_t n);
void *memccpy(void *dst, const void *src, int c, size_t count);
int memcmp(const void *dst, const void *src, size_t n);
int memicmp(const void *buf1, const void *buf2, size_t count);
void * memchr(const void *s, int c, size_t n);

#endif // __STRING_H__