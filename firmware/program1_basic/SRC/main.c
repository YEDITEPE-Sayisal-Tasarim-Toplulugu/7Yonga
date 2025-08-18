#include <stdint.h>

volatile int data1 = 5;
volatile int data2 = 2;
volatile int data3 = 4;

void UART_send_string(const char *str);

int main( void ) {
    UART_send_string("Hello From Sram!\n");
    return 0;
}