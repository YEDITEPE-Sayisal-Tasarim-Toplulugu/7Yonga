#include "uart_driver.h"

#include "string.h"

#include <stdint.h>

/**
 * @brief Initialize UART driver
 * @param driver Pointer to UART driver structure
 * @param base_addr Base address of UART peripheral
 * @param system_clock System clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int uart_init(uart_driver_t *driver, uint32_t base_addr, uint32_t system_clock) {
    driver->base_addr = base_addr;
    driver->regs = (uart_regs_t *)(base_addr);
    driver->system_clock = system_clock;
    return 0;
}

/**
 * @brief Configure UART baud rate
 * @param driver Pointer to UART driver structure
 * @param baud_rate Desired baud rate in bps
 * @return 0 on success, -1 on error
 */
int uart_set_baud_rate(uart_driver_t *driver, uint32_t baud_rate) {
    int brate;
    brate = (driver->system_clock/baud_rate);
    driver->regs->CPB = brate;
    return 0;
}

/**
 * @brief Configure UART stop bits
 * @param driver Pointer to UART driver structure
 * @param stop_bits Stop bit configuration
 * @return 0 on success, -1 on error
 */
int uart_set_stop_bits(uart_driver_t *driver, uart_stop_bits_t stop_bits) {
    driver->regs->STP = stop_bits;
    return 0;
}

void uart_send_tx_valid(uart_driver_t *driver) {
    int ucfg;
    ucfg = driver->regs->CFG;
    ucfg = UART_CFG_SET_TX_ENABLE(ucfg);
    ucfg = UART_CFG_CLEAR_TX_COMPLETED(ucfg);
    driver->regs->CFG = ucfg;
}

/**
 * @brief Send a single byte via UART
 * @param driver Pointer to UART driver structure
 * @param data Byte to send
 * @return 0 on success, -1 on error
 */
int uart_send_byte(uart_driver_t *driver, uint8_t data) {
    driver->regs->TDR = data;
    uart_send_tx_valid(driver);
    return 0;
}

/**
 * @brief Send a single byte via UART and wait for tx complate
 * @param driver Pointer to UART driver structure
 * @param data Byte to send
 * @return 0 on success, -1 on error
 */
int uart_send_byte_and_wait(uart_driver_t *driver, uint8_t data) {
    uart_send_byte(driver, data);
    uart_wait_tx_complete(driver);
    return 0;
}

/**
 * @brief Send a string via UART
 * @param driver Pointer to UART driver structure
 * @param str Null-terminated string to send
 * @return Number of bytes sent, -1 on error
 */
int uart_send_string(uart_driver_t *driver, const char *str) {
    int bc=0;
    while (*str) {
        uart_send_byte_and_wait(driver, *str);
        bc++;
        str++;
    }
    return bc;
}

/**
 * @brief Send data buffer via UART
 * @param driver Pointer to UART driver structure
 * @param data Pointer to data buffer
 * @param length Number of bytes to send
 * @return Number of bytes sent, -1 on error
 */
int uart_send_data(uart_driver_t *driver, const uint8_t *data, uint32_t length) {
    int bc=0;
    while (length--) {
        uart_send_byte_and_wait(driver, *data);
        data++;
        bc++;
    }
    return bc;
}

/**
 * @brief Check if new data has been received
 * @param driver Pointer to UART driver structure
 * @return 1 if data available, 0 if no data, -1 on error
 */
int uart_is_data_available(uart_driver_t *driver) {
    int ucfg_data, rx_valid;
    ucfg_data = driver->regs->CFG;
    rx_valid = UART_CFG_READ_RX_RECEIVED(ucfg_data);
    return rx_valid;
}


/**
 * @brief Read received byte (non-blocking)
 * @param driver Pointer to UART driver structure
 * @param data Pointer to store received byte
 * @return 1 if byte received, 0 if no data, -1 on error
 */
int uart_receive_byte_nonblocking(uart_driver_t *driver, uint8_t *data) {
    if ( uart_is_data_available(driver) != 1 ) return 0;
    *data = driver->regs->RDR & 0xFF;
    return 1;
}

/**
 * @brief Read received byte (blocking)
 * @param driver Pointer to UART driver structure
 * @return Received byte (0-255) on success, -1 on error
 */
int uart_receive_byte(uart_driver_t *driver) {
    uint8_t data = 0;
    
    while (!uart_is_data_available(driver))
        ;
    
    uart_receive_byte_nonblocking(driver, &data);

    return data;
}

/**
 * @brief Check if transmit is completed
 * @param driver Pointer to UART driver structure
 * @return 1 if TX completed, 0 if TX busy, -1 on error
 */
int uart_is_tx_completed(uart_driver_t *driver) {
    int ucfg;
    int tx_comp;

    ucfg = driver->regs->CFG;
    tx_comp = UART_CFG_READ_TX_COMPLETED(ucfg);

    return tx_comp;
}

/**
 * @brief Wait for transmit completion
 * @param driver Pointer to UART driver structure
 * @return 0 on success, -1 on error
 */
int uart_wait_tx_complete(uart_driver_t *driver) {
    while (!uart_is_tx_completed(driver))
        ;
    return 0;
}

/**
 * @brief Clear receive flag
 * @param driver Pointer to UART driver structure
 */
void uart_clear_rx_flag(uart_driver_t *driver) {
    driver->regs->CFG = UART_CFG_CLEAR_RX_RECEIVED(driver->regs->CFG);
}

/**
 * @brief Clear transmit completion flag
 * @param driver Pointer to UART driver structure
 */
void uart_clear_tx_flag(uart_driver_t *driver) {
    driver->regs->CFG = UART_CFG_CLEAR_TX_COMPLETED(driver->regs->CFG);
}

int uart_is_ready(uart_driver_t *driver) {
    // return uart_is_tx_completed(driver);
    return 1;
}

//================================================================
// Printf-style Functions
//================================================================

/**
 * @brief Send formatted integer via UART
 * @param driver Pointer to UART driver structure
 * @param value Integer value to send
 * @return Number of characters sent, -1 on error
 */
int uart_print_int(uart_driver_t *driver, int32_t value) {
    char buf[PRINT_INT_ARRAY_SIZE];   // 32-bit int için yeterli (max: -2147483648)
    if (itoa(value, (unsigned char*)buf, sizeof(buf), 10) < 0)
        return -1;
    return uart_send_string(driver, buf);
}

/**
 * @brief Send formatted unsigned integer via UART
 * @param driver Pointer to UART driver structure
 * @param value Unsigned integer value to send
 * @return Number of characters sent, -1 on error
 */
int uart_print_uint(uart_driver_t *driver, uint32_t value) {
    char buf[PRINT_INT_ARRAY_SIZE];   // 32-bit unsigned max: 4294967295
    if (itoa((int)value, (unsigned char*)buf, sizeof(buf), 10) < 0)
        return -1;
    return uart_send_string(driver, buf);
}

/**
 * @brief Send formatted hexadecimal value via UART
 * @param driver Pointer to UART driver structure
 * @param value Value to send as hex
 * @param uppercase Use uppercase hex digits (A-F) if 1, lowercase (a-f) if 0
 * @return Number of characters sent, -1 on error
 */
int uart_print_hex(uart_driver_t *driver, uint32_t value, int uppercase) {
    char buf[PRINT_INT_ARRAY_SIZE];

    // itoa ile base=16 kullan
    if (itoa((int)value, (unsigned char*)buf, sizeof(buf), 16) < 0)
        return -1;

    // Eğer lowercase isteniyorsa, A-F -> a-f
    if (!uppercase) {
        for (char *p = buf; *p; p++) {
            if (*p >= 'A' && *p <= 'F')
                *p = *p - 'A' + 'a';
        }
    }

    return uart_send_string(driver, buf);
}

/**
 * @brief Send newline via UART
 * @param driver Pointer to UART driver structure
 * @return Number of characters sent (2), -1 on error
 */
int uart_println(uart_driver_t *driver) {
    return uart_send_string(driver, UART_NEWLINE);
}
