#include <stdint.h>

#define UART_BASE_ADDR 0x20000000
#define BUFFER_LENGTH 25600

volatile int buffer[BUFFER_LENGTH];

void putChar(char c) {
    *(volatile int*)(UART_BASE_ADDR+12) = c;
}

void putString(char *str) {
    while(*str) {
        putChar(*str);
        str++;
    }
}

int main( void )
{
    int succ=1;
    char *str_fail = "FAIL!";
    char *str_succ = "SUCC!";

    int i;
    for (i=0; i<BUFFER_LENGTH; i++) {
        buffer[i] = i;
    }

    for (i=0; i<BUFFER_LENGTH; i++) {
        buffer[i]++;
    }

    for (i=0; i<BUFFER_LENGTH; i++) {
        if (buffer[i]-1 != i) {
            succ = 0;
            break;
        }
    }

    if (succ)
        putString(str_succ);
    else
        putString(str_fail);

    return 0;
}