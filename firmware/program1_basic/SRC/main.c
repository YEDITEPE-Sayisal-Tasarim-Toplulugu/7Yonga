#include "Yonga7std.h"
#include <stdint.h>

#define UART_BAUDE_RATE               9600

uart_driver_t uart_driver;

int init( void ) {
    uart_init(&uart_driver, YONGA7_UART_BASE, YONGA7_SOC_PERIPHERAL_FREQUENCY);
    uart_set_baud_rate(&uart_driver, UART_BAUDE_RATE);
    uart_set_stop_bits(&uart_driver, UART_STOP_BITS_1);

    return 1;
}


int main( void ) {
    init();
    uart_send_string(&uart_driver, "Hello From Sram!\n");
    return 0;
}


