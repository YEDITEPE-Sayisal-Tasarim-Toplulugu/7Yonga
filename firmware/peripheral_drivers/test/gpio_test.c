#include "gpio_driver.h"
#include <stdint.h>

// GPIO base address - bu projeye özel olarak ayarlanmalı
#define GPIO_BASE_ADDR    0x40001000  // Örnek adres - gerçek adresi ayarlayın

// Test utility functions
void delay_cycles(uint32_t cycles) {
    volatile uint32_t i;
    for (i = 0; i < cycles; i++) {
        // Simple delay loop
        __asm volatile ("nop");
    }
}

void test_basic_gpio_operations(gpio_driver_t *gpio) {
    uint16_t test_pattern;
    uint16_t read_back;
    
    // Test 1: Write and read back all zeros
    gpio_write_output_pins(gpio, 0x0000);
    read_back = gpio_read_output_pins(gpio);
    // Note: In real test, you would check read_back == 0x0000
    
    // Test 2: Write and read back all ones
    gpio_write_output_pins(gpio, 0xFFFF);
    read_back = gpio_read_output_pins(gpio);
    // Note: In real test, you would check read_back == 0xFFFF
    
    // Test 3: Walking ones pattern
    for (int i = 0; i < 16; i++) {
        test_pattern = (1U << i);
        gpio_write_output_pins(gpio, test_pattern);
        delay_cycles(1000);
        read_back = gpio_read_output_pins(gpio);
        // Note: In real test, you would check read_back == test_pattern
    }
    
    // Test 4: Walking zeros pattern
    for (int i = 0; i < 16; i++) {
        test_pattern = ~(1U << i);
        gpio_write_output_pins(gpio, test_pattern);
        delay_cycles(1000);
        read_back = gpio_read_output_pins(gpio);
        // Note: In real test, you would check read_back == test_pattern
    }
}

void test_individual_pin_operations(gpio_driver_t *gpio) {
    // Clear all pins first
    gpio_write_output_pins(gpio, 0x0000);
    
    // Test setting individual pins
    for (int pin = 0; pin < 16; pin++) {
        gpio_set_output_pin(gpio, pin);
        delay_cycles(500);
        
        // Verify pin is set
        uint8_t pin_state = gpio_read_output_pin(gpio, pin);
        // Note: In real test, you would check pin_state == 1
        
        gpio_clear_output_pin(gpio, pin);
        delay_cycles(500);
        
        // Verify pin is cleared
        pin_state = gpio_read_output_pin(gpio, pin);
        // Note: In real test, you would check pin_state == 0
    }
}

void test_toggle_operations(gpio_driver_t *gpio) {
    // Clear all pins first
    gpio_write_output_pins(gpio, 0x0000);
    
    // Test toggling each pin
    for (int pin = 0; pin < 16; pin++) {
        // Toggle pin - should go from 0 to 1
        gpio_toggle_output_pin(gpio, pin);
        uint8_t pin_state = gpio_read_output_pin(gpio, pin);
        // Note: In real test, you would check pin_state == 1
        
        // Toggle again - should go from 1 to 0  
        gpio_toggle_output_pin(gpio, pin);
        pin_state = gpio_read_output_pin(gpio, pin);
        // Note: In real test, you would check pin_state == 0
    }
}

void test_masked_operations(gpio_driver_t *gpio) {
    // Clear all pins first
    gpio_write_output_pins(gpio, 0x0000);
    
    // Test masked write: Set pins 0,2,4,6,8,10,12,14 to 1
    uint16_t mask = 0x5555;  // 0101010101010101
    uint16_t value = 0x5555; // 0101010101010101
    
    gpio_write_output_pins_masked(gpio, mask, value);
    uint16_t read_back = gpio_read_output_pins(gpio);
    // Note: In real test, you would check read_back == 0x5555
    
    // Test masked write: Set pins 1,3,5,7,9,11,13,15 to 1, keep others unchanged
    mask = 0xAAAA;   // 1010101010101010
    value = 0xAAAA;  // 1010101010101010
    
    gpio_write_output_pins_masked(gpio, mask, value);
    read_back = gpio_read_output_pins(gpio);
    // Note: In real test, you would check read_back == 0xFFFF
    
    // Test masked write: Clear pins 0,4,8,12, keep others unchanged
    mask = 0x1111;   // 0001000100010001
    value = 0x0000;  // 0000000000000000
    
    gpio_write_output_pins_masked(gpio, mask, value);
    read_back = gpio_read_output_pins(gpio);
    // Note: In real test, you would check read_back == 0xEEEE
}

void test_input_pins(gpio_driver_t *gpio) {
    // Read all input pins
    uint16_t input_state = gpio_read_input_pins(gpio);
    
    // Read individual input pins
    for (int pin = 0; pin < 16; pin++) {
        uint8_t pin_state = gpio_read_input_pin(gpio, pin);
        // Note: Input pin states depend on external connections
        // In a real system, you would connect known signals to verify
    }
}

void gpio_led_blink_demo(gpio_driver_t *gpio) {
    // Simple LED blinking demo
    // Assumes LEDs are connected to output pins
    
    for (int cycle = 0; cycle < 10; cycle++) {
        // Turn on all LEDs
        gpio_write_output_pins(gpio, 0xFFFF);
        delay_cycles(100000);
        
        // Turn off all LEDs  
        gpio_write_output_pins(gpio, 0x0000);
        delay_cycles(100000);
    }
    
    // Running light effect
    for (int cycle = 0; cycle < 5; cycle++) {
        for (int pin = 0; pin < 16; pin++) {
            gpio_write_output_pins(gpio, (1U << pin));
            delay_cycles(50000);
        }
        for (int pin = 14; pin >= 1; pin--) {
            gpio_write_output_pins(gpio, (1U << pin));
            delay_cycles(50000);
        }
    }
}

int main(void) {
    gpio_driver_t gpio_driver;
    
    // Initialize GPIO driver
    if (gpio_init(&gpio_driver, GPIO_BASE_ADDR) != 0) {
        // Initialization failed
        return -1;
    }
    
    // Run basic GPIO tests
    test_basic_gpio_operations(&gpio_driver);
    
    // Test individual pin operations
    test_individual_pin_operations(&gpio_driver);
    
    // Test toggle operations
    test_toggle_operations(&gpio_driver);
    
    // Test masked operations
    test_masked_operations(&gpio_driver);
    
    // Test input pins
    test_input_pins(&gpio_driver);
    
    // LED blinking demo (if LEDs are connected)
    gpio_led_blink_demo(&gpio_driver);
    
    // Test completed - in a real system, you would report results
    return 0;
}