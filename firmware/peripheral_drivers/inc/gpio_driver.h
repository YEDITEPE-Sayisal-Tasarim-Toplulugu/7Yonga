#ifndef __GPIO_DRIVER_H__
#define __GPIO_DRIVER_H__

#include <stdint.h>

#define GPIO_IDR_OFFSET    0x00    // Input Data Register (Read-Only)
#define GPIO_ODR_OFFSET    0x04    // Output Data Register (Read-Write)

typedef struct {
    volatile uint32_t IDR;    // 0x00 - Input Data Register
    volatile uint32_t ODR;    // 0x04 - Output Data Register
} gpio_regs_t;

typedef struct {
    uint32_t base_addr;       // Base address of GPIO peripheral
    gpio_regs_t *regs;        // Pointer to GPIO registers
} gpio_driver_t;
#define GPIO_PIN_0     (1U << 0)
#define GPIO_PIN_1     (1U << 1)
#define GPIO_PIN_2     (1U << 2)
#define GPIO_PIN_3     (1U << 3)
#define GPIO_PIN_4     (1U << 4)
#define GPIO_PIN_5     (1U << 5)
#define GPIO_PIN_6     (1U << 6)
#define GPIO_PIN_7     (1U << 7)
#define GPIO_PIN_8     (1U << 8)
#define GPIO_PIN_9     (1U << 9)
#define GPIO_PIN_10    (1U << 10)
#define GPIO_PIN_11    (1U << 11)
#define GPIO_PIN_12    (1U << 12)
#define GPIO_PIN_13    (1U << 13)
#define GPIO_PIN_14    (1U << 14)
#define GPIO_PIN_15    (1U << 15)

#define GPIO_ALL_INPUT_PINS   0x0000FFFF
#define GPIO_ALL_OUTPUT_PINS  0x0000FFFF

int gpio_init(gpio_driver_t *driver, uint32_t base_addr);

uint16_t gpio_read_input_pins(gpio_driver_t *driver);

uint8_t gpio_read_input_pin(gpio_driver_t *driver, uint8_t pin);

void gpio_write_output_pins(gpio_driver_t *driver, uint16_t value);

void gpio_set_output_pin(gpio_driver_t *driver, uint8_t pin);

void gpio_clear_output_pin(gpio_driver_t *driver, uint8_t pin);

void gpio_toggle_output_pin(gpio_driver_t *driver, uint8_t pin);

uint16_t gpio_read_output_pins(gpio_driver_t *driver);

uint8_t gpio_read_output_pin(gpio_driver_t *driver, uint8_t pin);

void gpio_write_output_pins_masked(gpio_driver_t *driver, uint16_t mask, uint16_t value);

#define GPIO_PIN_IS_HIGH(pins, pin_num)    (((pins) >> (pin_num)) & 1U)
#define GPIO_PIN_IS_LOW(pins, pin_num)     (!GPIO_PIN_IS_HIGH(pins, pin_num))

#endif // __GPIO_DRIVER_H__