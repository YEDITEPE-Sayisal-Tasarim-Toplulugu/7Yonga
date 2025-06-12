#include "string.h"
#include <stdint.h>

int tolower(int ch)
{
    if ( (unsigned int)(ch - 'A') < 26u )
        ch += 'a' - 'A';
    return ch;
}

int toupper(int ch) 
{
    if ( (unsigned int)(ch - 'a') < 26 )
        ch += 'A' - 'a';

    return ch;
}

size_t strlen(const char * str)
{
    const char * s;

    if(!str) 
        return 0;

    for(s = str; *s; ++ s)
        ;

    return s - str;
}

size_t strnlen(const char * str, size_t n)
{
    const char * s;

    if(n == 0 || !str) 
        return 0;

    for(s = str; *s && n; ++ s, -- n)
        ;

    return s - str;
}

int strcmp(const char* s1, const char* s2)
{
    while(*s1 == *s2)
    {
        if(*s1 == 0) 
            return 0;

        s1 ++;
        s2 ++;
    }

    return *s1 - *s2;
}

int strncmp(const char * s1, const char * s2, size_t n)
{
    if(n == 0) 
        return 0;

    do
    {
        if(*s1 != *s2 ++) 
            return *s1 - *--s2;
        if(*s1++ == 0) 
            break;
    }
    while (-- n != 0);

    return 0;
}

int strcasecmp(const char* s1, const char* s2)
{
    while(tolower(*s1) == tolower(*s2))
    {
        if(*s1 == 0) 
            return 0;

        s1 ++;
        s2 ++;
    }

    return tolower(*s1) - tolower(*s2);
}

int strncasecmp(const char * s1, const char * s2, size_t n)
{
    if(n == 0) 
        return 0;

    do
    {
        if(tolower(*s1) != tolower(*s2++)) 
            return tolower(*s1) - tolower(*--s2);
        if(*s1++ == 0) 
            break;
    }
    while (-- n != 0);

    return 0;
}

char *strcat(char *dst, char *src)
{
    char *cp = dst;
    char *cr = src;
    
    while (*cp) 
        cp++;
    
    while ((*cp++ = *cr++));
    
    return dst;
}

char *strncat(char *s1, char *s2, size_t count)
{
    char *start = s1;

    while (*s1++);

    s1--;

    while (count--)
        if (!(*s1++ = *s2++)) 
            return start;

    *s1 = '\0';
    return start;
}

char * strcpy(char * dst, char * src)
{
    char *pp = dst;
    char *pr = src;

	while ((*pp++=*pr++))
		;
	
    return dst;
}

char * strncpy(char * dst, char * src, size_t n)
{
    if(n != 0)
    {
        char * d = dst;
        const char * s = src;

        do
        {
            if((*d ++ = *s ++) == 0)
            {
                while (-- n != 0) *d ++ = 0;
                break;
            }
        }
        while(-- n != 0);
    }

    return dst;
}

char * strrchr(char *cp, int ch)
{
    char *save;
    char c;

    for (save = (char *) 0; (c = *cp); cp++) 
    {
        if (c == ch)
            save = (char *) cp;
    }

    return save;
}

char *strchr(char *s, int c)
{
    do 
    {
        if (*s == c)
            return (char*)s;
    } 
    while (*s++);
    
    return 0;
}

int atoi(const char *str)
{
    unsigned int val = 0;

    while ('0' <= *str && *str <= '9') 
    {
        val *= 10;
        val += *str++ - '0';
    }

    return (int)val;
}

int atoi_hex(const char *str)
{
    unsigned int sum = 0;
    unsigned int leftshift = 0;
    char *s = (char*)str;
    char c;
    
    // Find the end
    while (*s)
        s++;

    // Backwards through the string
    while(s != str)
    {
        s--;
        c = *s;

        if((c >= '0') && (c <= '9'))
            sum += (c-'0') << leftshift;
        else if((c >= 'A') && (c <= 'F'))
            sum += (c-'A'+10) << leftshift;
        else if((c >= 'a') && (c <= 'f'))
            sum += (c-'a'+10) << leftshift;
        else
            break;
        
        leftshift+=4;
    }

    return (int)sum;
}

void reverse(char s[])
{
    int i, j;
    char c;

    for (i = 0, j = strlen(s)-1; i<j; i++, j--) 
    {
        c = s[i];
        s[i] = s[j];
        s[j] = c;
    }
}

void reverse_wlen(char* str, int len) {
    int start = 0;
    int end = len - 1;
    while (start < end) {
        char temp = str[start];
        str[start] = str[end];
        str[end] = temp;
        start++;
        end--;
    }
}

char * itoa(int n, char *s, int base)
{
    int i, sign;

    if ((sign = n) < 0)
        n = -n;

    i = 0;
    do 
    {      
        s[i++] = n % 10 + '0';
    } 
    while ((n /= 10) > 0);
    
    if (sign < 0)
        s[i++] = '-';
    
    s[i] = '\0';
    reverse(s);

    return s;
}

void int2hex(uint32_t num, char *outbuf)
{

    int i = 12;
    int j = 0;
    int base = 16;

    char sign = (num < 0) ? '-' : ' ';

    do{
        outbuf[i] = "0123456789ABCDEF"[num % base];
        i--;
        num = num/base;
    }while( num > 0);

    if(sign != ' '){
        outbuf[0] = sign;
        ++j;
    }

    while( ++i < 13){
       outbuf[j++] = outbuf[i];
    }

    outbuf[j] = 0;

}

void hexToStrDigits(unsigned int num, char* str, int numDigits) {
    int i = 0;

    do {
        int digit = num % 16;
        str[i++] = (digit < 10) ? (digit + '0') : (digit - 10 + 'A');
        num = num / 16;
    } while (num);

    // Add leading zeros if necessary
    while (i < numDigits) {
        str[i++] = '0';
    }

    str[i] = '\0';

    reverse_wlen(str, i);
}

// MEM COMMANDS
void *memset(void *p, int c, size_t n)
{
    char *pb = (char *) p;
    char *pbend = pb + n;

    while (pb != pbend) 
        *pb++ = c;
    return p;
}

void *memmove(void *v_dst, const void *v_src, size_t length)
{
    char *src               = (char *)v_src;
    char *dst               = (char *)v_dst;
    unsigned int *src32     = (unsigned int *)v_src;
    unsigned int *dst32     = (unsigned int *)v_dst;

    // No need to copy if src = dst or no length
    if (!length || v_src == v_dst)
        return v_dst;

    // Word aligned source & dest?
    if ((((unsigned long)dst & 3) == 0) && (((unsigned long)src & 3) == 0) && (length >= 4))
    {
        // How many full words can be copied?
        unsigned int len32 = length >> 2;

        // Move from lower address to higher address
        if (src < dst)
        {
            // Copy from end 
            for (src32 += len32, dst32 += len32; len32; --len32)
                *--dst32 = *--src32;

            src+= (length & ~3);
            dst+= (length & ~3);
        }
        // Move from higher address to lower address
        else
        {
            // Copy from start 
            for (; len32; --len32)
                *dst32++ = *src32++;

            src = (char *)src32;
            dst = (char *)dst32;
        }

        // There might be some bytes left over
        length -= (length & ~3);
    }

    // Byte copy if not aligned (or odd length)
    if (length)
    {
        // Move from lower address to higher address
        if (src < dst)
        {
            // Copy from end 
            for (src += length, dst += length; length; --length)
                *--dst = *--src;
        }
        // Move from higher address to lower address
        else
        {
            // Copy from start 
            for (; length; --length)
                *dst++ = *src++;
        }
    }

    return v_dst;
}

void *memcpy(void *dst, const void *src, size_t n)
{
    void *ret = dst;

    if (sizeof(unsigned long) == 4 && (n > 4) && (((unsigned long)dst) & 3) == 0 && (((unsigned long)src) & 3) == 0)
    {
        while (n >= 4)
        {
            *(unsigned long *)dst = *(unsigned long *)src;
            dst = (char *) dst + 4;
            src = (char *) src + 4;
            n -= 4;
        }
    }

    while (n--)
    {
        *(char *)dst = *(char *)src;
        dst = (char *) dst + 1;
        src = (char *) src + 1;
    }

    return ret;
}

void *memccpy(void *dst, const void *src, int c, size_t count)
{
    while (count && (*((char *) (dst = (char *) dst + 1) - 1) =
        *((char *)(src = (char *) src + 1) - 1)) != (char) c)
    count--;

    return count ? dst : 0;
}

int memcmp(const void *dst, const void *src, size_t n)
{
    if (!n) return 0;

    while (--n && *(char *) dst == *(char *) src)
    {
        dst = (char *) dst + 1;
        src = (char *) src + 1;
    }

    return *((unsigned char *) dst) - *((unsigned char *) src);
}

int memicmp(const void *buf1, const void *buf2, size_t count)
{
    int f = 0, l = 0;
    const unsigned char *dst = (const unsigned char*)buf1;
    const unsigned char *src = (const unsigned char*)buf2;

    while (count-- && f == l)
    {
        f = tolower(*dst++);
        l = tolower(*src++);
    }

    return f - l;
}

void * memchr(const void *s, int c, size_t n)
{
    if (n != 0) 
    {
        const unsigned char *p = (const unsigned char*)s;

        do 
        {
            if (*p++ == c)
                return ((void *)(p - 1));
        } 
        while (--n != 0);
    }

    return 0;
}