#include <stdint.h>

#define UART_BASE_ADDR 0x20000000


void putChar(char c) {
    *(volatile int*)(UART_BASE_ADDR+12) = c;
}

void putString(char *str) {
    while(*str) {
        while (*(volatile int*)(UART_BASE_ADDR+4) & 1) // tx-buffer full
            ;
        putChar(*str);
        str++;
    }
}

int main( void )
{
    char *str = "STR!\n\r";

    int i;
    for (i=0; i<20; i++) {
        putString(str);
    }

    return 0;
}