#include "gpio_driver.h"

//================================================================
// Private Functions
//================================================================

/**
 * @brief Validate pin number
 * @param pin Pin number to validate
 * @return 1 if valid (0-15), 0 if invalid
 */
static inline int gpio_is_valid_pin(uint8_t pin) {
    return (pin <= 15);
}

//================================================================
// Public Functions
//================================================================

int gpio_init(gpio_driver_t *driver, uint32_t base_addr) {
    // Validate parameters
    if (driver == NULL) {
        return -1;
    }
    
    // Initialize driver structure
    driver->base_addr = base_addr;
    driver->regs = (gpio_regs_t *)base_addr;
    
    // Initialize output pins to 0 (all low)
    gpio_write_output_pins(driver, 0x0000);
    
    return 0;
}

uint16_t gpio_read_input_pins(gpio_driver_t *driver) {
    if (driver == NULL || driver->regs == NULL) {
        return 0;
    }
    
    // Read IDR register and mask to get only lower 16 bits
    // According to spec: IDR[15:0] = input pins, IDR[31:16] = always 0
    return (uint16_t)(driver->regs->IDR & 0x0000FFFF);
}

uint8_t gpio_read_input_pin(gpio_driver_t *driver, uint8_t pin) {
    if (driver == NULL || !gpio_is_valid_pin(pin)) {
        return 0;
    }
    
    uint16_t input_pins = gpio_read_input_pins(driver);
    return GPIO_PIN_IS_HIGH(input_pins, pin) ? 1 : 0;
}

void gpio_write_output_pins(gpio_driver_t *driver, uint16_t value) {
    if (driver == NULL || driver->regs == NULL) {
        return;
    }
    
    // Write to ODR register
    // According to spec: ODR[15:0] controls output pins, ODR[31:16] ignored
    driver->regs->ODR = (uint32_t)value;
}

void gpio_set_output_pin(gpio_driver_t *driver, uint8_t pin) {
    if (driver == NULL || !gpio_is_valid_pin(pin)) {
        return;
    }
    
    // Read current state, set the bit, write back
    uint16_t current_pins = gpio_read_output_pins(driver);
    current_pins |= (1U << pin);
    gpio_write_output_pins(driver, current_pins);
}

void gpio_clear_output_pin(gpio_driver_t *driver, uint8_t pin) {
    if (driver == NULL || !gpio_is_valid_pin(pin)) {
        return;
    }
    
    // Read current state, clear the bit, write back
    uint16_t current_pins = gpio_read_output_pins(driver);
    current_pins &= ~(1U << pin);
    gpio_write_output_pins(driver, current_pins);
}

void gpio_toggle_output_pin(gpio_driver_t *driver, uint8_t pin) {
    if (driver == NULL || !gpio_is_valid_pin(pin)) {
        return;
    }
    
    // Read current state, toggle the bit, write back
    uint16_t current_pins = gpio_read_output_pins(driver);
    current_pins ^= (1U << pin);
    gpio_write_output_pins(driver, current_pins);
}

uint16_t gpio_read_output_pins(gpio_driver_t *driver) {
    if (driver == NULL || driver->regs == NULL) {
        return 0;
    }
    
    // Read ODR register and mask to get only lower 16 bits
    return (uint16_t)(driver->regs->ODR & 0x0000FFFF);
}

uint8_t gpio_read_output_pin(gpio_driver_t *driver, uint8_t pin) {
    if (driver == NULL || !gpio_is_valid_pin(pin)) {
        return 0;
    }
    
    uint16_t output_pins = gpio_read_output_pins(driver);
    return GPIO_PIN_IS_HIGH(output_pins, pin) ? 1 : 0;
}

void gpio_write_output_pins_masked(gpio_driver_t *driver, uint16_t mask, uint16_t value) {
    if (driver == NULL) {
        return;
    }
    
    // Read current output state
    uint16_t current_pins = gpio_read_output_pins(driver);
    
    // Clear the bits specified by mask
    current_pins &= ~mask;
    
    // Set the new values for masked bits
    current_pins |= (value & mask);
    
    // Write back
    gpio_write_output_pins(driver, current_pins);
}