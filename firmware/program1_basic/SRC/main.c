#include "Yonga7std.h"
#include <stdint.h>

#define UART_BAUDE_RATE                 9600
#define QSPI_PRESCALER                  63

uart_driver_t uart_driver;
qspi_driver_t qspi_driver;

FLASH_RDID_DATA flash_rdid_data;

int init( void ) {
    uart_init(&uart_driver, YONGA7_UART_BASE, YONGA7_SOC_PERIPHERAL_FREQUENCY);
    uart_set_baud_rate(&uart_driver, UART_BAUDE_RATE);
    uart_set_stop_bits(&uart_driver, UART_STOP_BITS_1);

    QSPI_init(&qspi_driver, YONGA7_QSPI_BASE, YONGA7_SOC_PERIPHERAL_FREQUENCY, QSPI_PRESCALER);

    return 1;
}


int main( void ) {
    init();
    uart_send_string(&uart_driver, "Hello From Sram!\n");
    FLASH_read_REMS(&qspi_driver, &flash_rdid_data);
    uart_print_hex(&uart_driver, flash_rdid_data.ManufactureID, 1);
    uart_println(&uart_driver);
    uart_print_hex(&uart_driver, flash_rdid_data.DeviceID, 1);
    uart_println(&uart_driver);
    //FLASH_read_RES(&qspi_driver);
    uart_send_string(&uart_driver, "done.\n");
    
    return 0;
}
