#ifndef __UART_DRIVER_H__
#define __UART_DRIVER_H__

#include <stdint.h>

#define UART_CPB_OFFSET    0x00    // Clock-per-bit register
#define UART_STP_OFFSET    0x04    // Stop-bit register
#define UART_RDR_OFFSET    0x08    // Read data register (Read-Only)
#define UART_TDR_OFFSET    0x0C    // Transmit data register
#define UART_CFG_OFFSET    0x10    // Configuration register

typedef struct {
    volatile uint32_t CPB;    // 0x00 - Clock-per-bit register
    volatile uint32_t STP;    // 0x04 - Stop-bit register
    volatile uint32_t RDR;    // 0x08 - Read data register
    volatile uint32_t TDR;    // 0x0C - Transmit data register
    volatile uint32_t CFG;    // 0x10 - Configuration register
} uart_regs_t;

typedef struct {
    uint32_t base_addr;       // Base address of UART peripheral
    uart_regs_t *regs;        // Pointer to UART registers
    uint32_t system_clock;    // System clock frequency in Hz
} uart_driver_t;


typedef enum {
    UART_STOP_BITS_1   = 0,  // 1 stop bit
    UART_STOP_BITS_1_5 = 1,  // 1.5 stop bits
    UART_STOP_BITS_2   = 2   // 2 stop bits (any value >= 2)
} uart_stop_bits_t;

#define UART_CFG_TX_ENABLE      (1U << 0)  // Transmit enable
#define UART_CFG_RX_RECEIVED    (1U << 1)  // Data received flag (set by HW, clear by SW)
#define UART_CFG_TX_COMPLETED   (1U << 2)  // Transmit completed flag (set by HW, clear by SW)

#define UART_BAUD_9600      9600
#define UART_BAUD_19200     19200
#define UART_BAUD_38400     38400
#define UART_BAUD_57600     57600
#define UART_BAUD_115200    115200
#define UART_BAUD_230400    230400
#define UART_BAUD_460800    460800
#define UART_BAUD_921600    921600
#define UART_BAUD_1000000   1000000



/**
 * @brief Initialize UART driver
 * @param driver Pointer to UART driver structure
 * @param base_addr Base address of UART peripheral
 * @param system_clock System clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int uart_init(uart_driver_t *driver, uint32_t base_addr, uint32_t system_clock);

/**
 * @brief Configure UART baud rate
 * @param driver Pointer to UART driver structure
 * @param baud_rate Desired baud rate in bps
 * @return 0 on success, -1 on error
 */
int uart_set_baud_rate(uart_driver_t *driver, uint32_t baud_rate);

/**
 * @brief Configure UART stop bits
 * @param driver Pointer to UART driver structure
 * @param stop_bits Stop bit configuration
 * @return 0 on success, -1 on error
 */
int uart_set_stop_bits(uart_driver_t *driver, uart_stop_bits_t stop_bits);

/**
 * @brief Send a single byte via UART
 * @param driver Pointer to UART driver structure
 * @param data Byte to send
 * @return 0 on success, -1 on error
 */
int uart_send_byte(uart_driver_t *driver, uint8_t data);

/**
 * @brief Send a string via UART
 * @param driver Pointer to UART driver structure
 * @param str Null-terminated string to send
 * @return Number of bytes sent, -1 on error
 */
int uart_send_string(uart_driver_t *driver, const char *str);

/**
 * @brief Send data buffer via UART
 * @param driver Pointer to UART driver structure
 * @param data Pointer to data buffer
 * @param length Number of bytes to send
 * @return Number of bytes sent, -1 on error
 */
int uart_send_data(uart_driver_t *driver, const uint8_t *data, uint32_t length);

/**
 * @brief Check if new data has been received
 * @param driver Pointer to UART driver structure
 * @return 1 if data available, 0 if no data, -1 on error
 */
int uart_is_data_available(uart_driver_t *driver);

/**
 * @brief Read received byte (blocking)
 * @param driver Pointer to UART driver structure
 * @return Received byte (0-255) on success, -1 on error
 */
int uart_receive_byte(uart_driver_t *driver);

/**
 * @brief Read received byte (non-blocking)
 * @param driver Pointer to UART driver structure
 * @param data Pointer to store received byte
 * @return 1 if byte received, 0 if no data, -1 on error
 */
int uart_receive_byte_nonblocking(uart_driver_t *driver, uint8_t *data);

/**
 * @brief Check if transmit is completed
 * @param driver Pointer to UART driver structure
 * @return 1 if TX completed, 0 if TX busy, -1 on error
 */
int uart_is_tx_completed(uart_driver_t *driver);

/**
 * @brief Wait for transmit completion
 * @param driver Pointer to UART driver structure
 * @return 0 on success, -1 on error
 */
int uart_wait_tx_complete(uart_driver_t *driver);

/**
 * @brief Clear receive flag
 * @param driver Pointer to UART driver structure
 */
void uart_clear_rx_flag(uart_driver_t *driver);

/**
 * @brief Clear transmit completion flag
 * @param driver Pointer to UART driver structure
 */
void uart_clear_tx_flag(uart_driver_t *driver);

//================================================================
// Printf-style Functions
//================================================================

/**
 * @brief Send formatted integer via UART
 * @param driver Pointer to UART driver structure
 * @param value Integer value to send
 * @return Number of characters sent, -1 on error
 */
int uart_print_int(uart_driver_t *driver, int32_t value);

/**
 * @brief Send formatted unsigned integer via UART
 * @param driver Pointer to UART driver structure
 * @param value Unsigned integer value to send
 * @return Number of characters sent, -1 on error
 */
int uart_print_uint(uart_driver_t *driver, uint32_t value);

/**
 * @brief Send formatted hexadecimal value via UART
 * @param driver Pointer to UART driver structure
 * @param value Value to send as hex
 * @param uppercase Use uppercase hex digits (A-F) if 1, lowercase (a-f) if 0
 * @return Number of characters sent, -1 on error
 */
int uart_print_hex(uart_driver_t *driver, uint32_t value, int uppercase);

/**
 * @brief Send newline via UART
 * @param driver Pointer to UART driver structure
 * @return Number of characters sent (2), -1 on error
 */
int uart_println(uart_driver_t *driver);

//================================================================
// Utility Macros
//================================================================
#define UART_NEWLINE "\r\n"

// Helper macros for quick printf-style debugging
#define uart_debug_str(uart, str)     uart_send_string(uart, str)
#define uart_debug_int(uart, val)     uart_print_int(uart, val)
#define uart_debug_hex(uart, val)     uart_print_hex(uart, val, 1)
#define uart_debug_ln(uart)           uart_println(uart)

#endif // __UART_DRIVER_H__