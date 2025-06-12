#ifndef __UART_DRIVER_H__
#define __UART_DRIVER_H__

#include "string.h"
#include <stdint.h>

typedef struct sUartDriver
{
    uint32_t CTRL;          // 0x00
/*
    // 0x00
    struct {
        unsigned int tx_en      : 1;
        unsigned int rx_en      : 1;
        unsigned int null       : 14;
        unsigned int baudeDiv   : 16;
    } CTRL;
*/
    // 0x04
    struct {
        unsigned int tx_full    : 1;
        unsigned int tx_empty   : 1;
        unsigned int rx_full    : 1;
        unsigned int rx_empty   : 1;
        unsigned int null       : 28;
    } STAT;

    uint32_t READ;          // 0x08
    uint32_t WRITE;         // 0x0c
} uartDriver;

//-----------------------------------------------------------------
// Prototypes
//-----------------------------------------------------------------
void uart_initial(int32_t base_addr, uint32_t baud_div);

void send_byte(uint8_t value);
void send_char(char value);

void print_string(char *str);
void print_int(uint32_t integer_value);
void print_hex(int num);

int read_char(int printTheKey);

int uart_rx_full(void);
int uart_rx_empty(void);
int uart_tx_full(void);
int uart_tx_empty(void);

#endif