#include "uart_driver.h"
#include <stdint.h>

static volatile uartDriver *uart_driver;

void uart_initial(int32_t base_addr, uint32_t baud_div)
{
    uart_driver = (volatile uartDriver*)base_addr;

    uint32_t ctr_data = 3 + (baud_div << 16);
    uart_driver->CTRL = ctr_data;
    /*
    uart_driver->CTRL.tx_en = 1;
    uart_driver->CTRL.rx_en = 1;
    uart_driver->CTRL.baudeDiv = baud_div;
    */
}

void send_char(char value)
{
    while (uart_tx_full())
        ;

	uart_driver->WRITE = value;
}

void print_string(char *str)
{
	do
		send_char(*str);
	while(*str++);
}

int read_char(int printTheKey)
{
    if (uart_rx_empty())
        return 0;
    else
    {
        int c = (uint8_t)uart_driver->READ;
        
        if (printTheKey)
            if ((c != '\n') & (c != '\r'))
            {
                send_char(c);
            }
        return c;
    }
}

int uart_tx_full(void)
{
    return uart_driver->STAT.tx_full;
}

int uart_tx_empty(void)
{
    return uart_driver->STAT.tx_empty;
}

int uart_rx_full(void)
{
    return uart_driver->STAT.rx_full;
}

int uart_rx_empty(void)
{
    return uart_driver->STAT.rx_empty;
}

