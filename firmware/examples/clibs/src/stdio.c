/*
    *  This version implements the following printf features:
    *
    *	%d	decimal conversion
    *	%u	unsigned conversion
    *	%x	hexadecimal conversion
    *	%X	hexadecimal conversion with capital letters
    *	%o	octal conversion
    *	%c	character
    *	%s	string
    *	%m.n	field width, precision
    *	%-m.n	left adjustment
    *	%0m.n	zero-padding
    *	%*.*	width and precision taken from arguments
*/

#include "stdio.h"

#include "string.h"
#include <stdint.h>
#include <stdarg.h> // Include the <stdarg.h> header for va_list

#define INT_TYPE 	int32_t
#define UINT_TYPE 	uint32_t

typedef int boolean_t;
#define TRUE 1
#define FALSE 0

#define isdigit(d) ((d) >= '0' && (d) <= '9')
#define Ctod(c) ((c) - '0')
#define MAXBUF (sizeof(INT_TYPE) * 8)		 /* enough for binary */
#define MAXBUF_LONG 50

#define MAX_INTEGER_CHARACTER 20

static void (*conslog_putc)(char);
static int (*conslog_readc)(void);

boolean_t	_doprnt_truncates = FALSE;

void printnum(
	register unsigned int	u,
	register int		base,
	void			(*putc)(char));

void
printnum(
	register unsigned int	u,		/* number to print */
	register int		base,
	void			(*putc)(char))
{
	char	buf[MAXBUF];	/* build number here */
	register char *	p = &buf[MAXBUF-1];
	static char digs[] = "0123456789abcdef";

	do {
	    *p-- = digs[u % base];
	    u /= base;
	} while (u != 0);

	while (++p != &buf[MAXBUF])
	    (*putc)(*p);

}

void printfloat(float num, void (*putc)(char)) {
    // Tam sayı ve ondalık kısmı ayırmak için
    int int_part = (int)num;
    float frac_part = num - int_part;

    // Tam sayı kısmını yazdır
    if (int_part == 0) {
		(*putc)('0');
    } else {
        char buffer[12];
        int index = 0;
        if (int_part < 0) {
			(*putc)('-');
            int_part = -int_part;
        }
        while (int_part > 0) {
            buffer[index++] = '0' + (int_part % 10);
            int_part /= 10;
        }
        for (int i = index - 1; i >= 0; i--) {
			(*putc)(buffer[i]);
        }
    }

    // Ondalık noktayı yazdır
	(*putc)('.');

    // Ondalık kısmı yazdır
    for (int i = 0; i < 6; i++) { // 6 basamak hassasiyet
        frac_part *= 10;
        int digit = (int)frac_part;
		(*putc)(('0' + digit));
        frac_part -= digit;
    }
}

void _doprnt(
	register const char	*fmt,
	va_list			*argp,
						/* character output routine */
	void			(*putc)(char),
	int			radix)		/* default radix - for '%r' */
{
	int		length;
	int		prec;
	boolean_t	ladjust;
	char		padc;
	long		n;
	unsigned long	u;
	int		plus_sign;
	int		sign_char;
	boolean_t	altfmt, truncate;
	int		base;
	register char	c;
	int		capitals;

	while ((c = *fmt) != '\0') {
	    if (c != '%') {
		(*putc)(c);
		fmt++;
		continue;
	    }

	    fmt++;

	    length = 0;
	    prec = -1;
	    ladjust = FALSE;
	    padc = ' ';
	    plus_sign = 0; // a6
	    sign_char = 0;
	    altfmt = FALSE;

	    while (TRUE) {
		c = *fmt;
		if (c == '#') {
		    altfmt = TRUE;
		}
		else if (c == '-') {
		    ladjust = TRUE;
		}
		else if (c == '+') {
		    plus_sign = '+';
		}
		else if (c == ' ') {
		    if (plus_sign == 0)
			plus_sign = ' ';
		}
		else
		    break;
		fmt++;
	    }

	    if (c == '0') {
		padc = '0';
		c = *++fmt;
	    }

	    if (isdigit(c)) {
		while(isdigit(c)) {
		    length = 10 * length + Ctod(c);
		    c = *++fmt;
		}
	    }
	    else if (c == '*') {
		length = va_arg(*argp, int);
		c = *++fmt;
		if (length < 0) {
		    ladjust = !ladjust;
		    length = -length;
		}
	    }

	    if (c == '.') {
		c = *++fmt;
		if (isdigit(c)) {
		    prec = 0;
		    while(isdigit(c)) {
			prec = 10 * prec + Ctod(c);
			c = *++fmt;
		    }
		}
		else if (c == '*') {
		    prec = va_arg(*argp, int);
		    c = *++fmt;
		}
	    }

	    if (c == 'l')
			c = *fmt++;	/* need it if sizeof(int) < sizeof(long) */

	    truncate = FALSE;
	    capitals=0;		/* Assume lower case printing */

	    switch(c) {
		case 'f':
		{
			int _f = va_arg(*argp, int);
			float *fp = (float *)&_f;
			float f = *fp;
			
			printfloat(f, putc);
			break;
		}
		case 'l':
		{
			
		}
		case 'b':
		case 'B':
		{
		    register char *p;
		    boolean_t	  any;
		    register int  i;

		    u = va_arg(*argp, unsigned long);
		    p = va_arg(*argp, char *);
		    base = *p++;
		    printnum(u, base, putc);

		    if (u == 0)
			break;

		    any = FALSE;
		    while ((i = *p++) != '\0') {
			if (*fmt == 'B')
			    i = 33 - i;
			if (*p <= 32) {
			    /*
			     * Bit field
			     */
			    register int j;
			    if (any)
				(*putc)(',');
			    else {
				(*putc)('<');
				any = TRUE;
			    }
			    j = *p++;
			    if (*fmt == 'B')
				j = 32 - j;
			    for (; (c = *p) > 32; p++)
				(*putc)(c);
			    printnum((unsigned)( (u>>(j-1)) & ((2<<(i-j))-1)),
					base, putc);
			}
			else if (u & (1<<(i-1))) {
			    if (any)
				(*putc)(',');
			    else {
				(*putc)('<');
				any = TRUE;
			    }
			    for (; (c = *p) > 32; p++)
				(*putc)(c);
			}
			else {
			    for (; *p > 32; p++)
				continue;
			}
		    }
		    if (any)
			(*putc)('>');
		    break;
		}

		case 'c':
		    c = va_arg(*argp, int);
		    (*putc)(c);
		    break;

		case 's':
		{
		    register char *p;
		    register char *p2;

		    if (prec == -1)
			prec = 0x7fffffff;	/* MAXINT */

		    p = va_arg(*argp, char *);

		    if (p == (char *)0)
			p = "";

		    if (length > 0 && !ladjust) {
			n = 0;
			p2 = p;

			for (; *p != '\0'; p++)
			    n++;

			p = p2;

			while (n < length) {
			    (*putc)(' ');
			    n++;
			}
		    }

		    n = 0;

		    while (*p != '\0') {
			if ((length > 0 && n > length))
			    break;

			(*putc)(*p++);
		    }

		    if (n < length && ladjust) {
			while (n < length) {
			    (*putc)(' ');
			    n++;
			}
		    }

		    break;
		}

		case 'o':
		    truncate = _doprnt_truncates;
		case 'O':
		    base = 8;
		    goto print_unsigned;

		case 'd':
		    truncate = _doprnt_truncates;
		case 'D':
		    base = 10;
		    goto print_signed;

		case 'u':
		    truncate = _doprnt_truncates;
		case 'U':
		    base = 10;
		    goto print_unsigned;

		case 'p':
		    altfmt = TRUE;
		case 'x':
		    truncate = _doprnt_truncates;
		    base = 16;
		    goto print_unsigned;

		case 'X':
		    base = 16;
		    capitals=16;	/* Print in upper case */
		    goto print_unsigned;

		case 'z':
		    truncate = _doprnt_truncates;
		    base = 16;
		    goto print_signed;
			
		case 'Z':
		    base = 16;
		    capitals=16;	/* Print in upper case */
		    goto print_signed;

		case 'r':
		    truncate = _doprnt_truncates;
		case 'R':
		    base = radix;
		    goto print_signed;

		case 'n':
		    truncate = _doprnt_truncates;
		case 'N':
		    base = radix;
		    goto print_unsigned;

		print_signed:
		    n = va_arg(*argp, INT_TYPE);
		    if (n >= 0) {
			u = n;
			sign_char = plus_sign;
		    }
		    else {
			u = -n;
			sign_char = '-';
		    }
		    goto print_num;

		print_unsigned:
		    u = va_arg(*argp, UINT_TYPE);
		    goto print_num;

		print_num:
		{
		    char	buf[MAXBUF];	/* build number here */
		    register char *	p = &buf[MAXBUF-1];
		    static char digits[] = "0123456789abcdef0123456789ABCDEF";
		    char *prefix = 0;

		    if (truncate) u = (long)((int)(u));

		    if (u != 0 && altfmt) {
			if (base == 8)
			    prefix = "0";
			else if (base == 16)
			    prefix = "0x";
		    }

		    do {
			/* Print in the correct case */
			*p-- = digits[(u % base)+capitals];
			u /= base;
		    } while (u != 0);

		    length -= (&buf[MAXBUF-1] - p);
		    if (sign_char)
			length--;
		    if (prefix)
			length -= strlen((const char *) prefix);

		    if (padc == ' ' && !ladjust) {
			/* blank padding goes before prefix */
			while (--length >= 0)
			    (*putc)(' ');
		    }
		    if (sign_char)
			(*putc)(sign_char);
		    if (prefix)
			while (*prefix)
			    (*putc)(*prefix++);
		    if (padc == '0') {
			/* zero padding goes after sign and prefix */
			while (--length >= 0)
			    (*putc)('0');
		    }
		    while (++p != &buf[MAXBUF])
			(*putc)(*p);

		    if (ladjust) {
			while (--length >= 0)
			    (*putc)(' ');
		    }
		    break;
		}

		case '\0':
		    fmt--;
		    break;

		default:
		    (*putc)(c);
	    }
	fmt++;
	}
}

void printf(const char *fmt, ...)
{
	va_list	listp;

	va_start(listp, fmt);
	_doprnt(fmt, &listp, conslog_putc, 10);
	va_end(listp);
}

static char *copybyte_str;

static void copybyte(char byte)
{
  *copybyte_str++ = byte;
  *copybyte_str = '\0';
}

int sprintf(char *buf, const char *fmt, ...)
{
        va_list listp;

        va_start(listp, fmt);
        
        copybyte_str = buf;
        _doprnt(fmt, &listp, copybyte, 16);

        va_end(listp);

        return strlen(buf);
}

/*
    putc: print char in printf
*/
void printf_init(void (*_putc)(char), int (*_readc)(void))
{
	conslog_putc = _putc;
	conslog_readc = _readc;
}


// Helper function to read a character from input
int readChar() {
    // Assuming you have a function to read a character from input, implement it here
    // For example, you might read a character from a serial port or a memory-mapped device
    // and return it.
    // Replace this with your actual implementation.
    // char c = read_character_from_input();
    // return c;

	int c = 0;
	while (!c)
		c = conslog_readc();

	return c;
}

// Helper function to check if a character is a whitespace character
int isWhitespace(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

int isBlackKey(char c) {
    return c == '\r';
}

// Helper function to convert a character to an integer
int charToInt(char c) {
    return c - '0';
}

// Helper function to convert a string to an integer
int stringToInt(char* str) {
    int result = 0;
    int sign = 1;

    // Handle negative numbers
    if (*str == '-') {
        sign = -1;
        str++;
    }

    // Convert string to integer
    while (*str != '\0') {
        result = result * 10 + charToInt(*str);
        str++;
    }

    return sign * result;
}

// scanf function implementation by @chatGPT
int scanf(const char* format, ...) {
    // Assuming you have a variable argument list implementation available
    // If not, you might need to implement it as well

    // Get the variable argument list
    va_list args;
    va_start(args, format);

    // Loop through the format string
    char c;
    while ((c = *format++) != '\0') {
        if (isWhitespace(c)) {
            // Skip whitespace characters
            continue;
        }
        else if (c == '%') {
            // Handle format specifiers
            c = *format++;
            if (c == 's') {
                // Handle string format specifier
                char* str = va_arg(args, char*);
				char getc;
                while (!isBlackKey(getc = readChar())) {
                    *str = getc;
                    str++;
                }
                *str = '\0'; // Null-terminate the string
            }
            else if (c == 'd') {
                // Handle integer format specifier
                int* num = va_arg(args, int*);
				char getc;
                char buffer[MAX_INTEGER_CHARACTER]; // Assuming a maximum integer length of 16 characters
                int i = 0;
				
				while (!isWhitespace(getc  = readChar())) {
					buffer[i] = getc;
					i++;
					if (i == MAX_INTEGER_CHARACTER) break;
				}
                buffer[i] = '\0'; // Null-terminate the buffer
                *num = stringToInt(buffer); // Convert the string to an integer
            }
        }
    }

    va_end(args);
    return 0; // Return 0 to indicate successful parsing
}

