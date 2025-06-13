#ifndef __TIMER_DRIVER_H__
#define __TIMER_DRIVER_H__

#include <stdint.h>

#define TIM_PRE_OFFSET    0x00    // Prescaler register
#define TIM_ARE_OFFSET    0x04    // Auto-reload register
#define TIM_CLR_OFFSET    0x08    // Clear register
#define TIM_ENA_OFFSET    0x0C    // Enable register
#define TIM_MOD_OFFSET    0x10    // Mode register
#define TIM_CNT_OFFSET    0x14    // Counter register (Read-Only)
#define TIM_EVN_OFFSET    0x18    // Event register (Read-Only)
#define TIM_EVC_OFFSET    0x1C    // Event clear register

typedef struct {
    volatile uint32_t PRE;    // 0x00 - Prescaler register
    volatile uint32_t ARE;    // 0x04 - Auto-reload register
    volatile uint32_t CLR;    // 0x08 - Clear register
    volatile uint32_t ENA;    // 0x0C - Enable register
    volatile uint32_t MOD;    // 0x10 - Mode register
    volatile uint32_t CNT;    // 0x14 - Counter register (RO)
    volatile uint32_t EVN;    // 0x18 - Event register (RO)
    volatile uint32_t EVC;    // 0x1C - Event clear register
} timer_regs_t;

typedef struct {
    uint32_t base_addr;       // Base address of Timer peripheral
    timer_regs_t *regs;       // Pointer to Timer registers
    uint32_t system_clock;    // System clock frequency in Hz
} timer_driver_t;

typedef enum {
    TIMER_MODE_DOWN = 0,      // Down counting mode
    TIMER_MODE_UP   = 1       // Up counting mode
} timer_mode_t;

#define TIMER_CLR_COUNTER     (1U << 0)  // Clear counter bit
#define TIMER_ENA_ENABLE      (1U << 0)  // Timer enable bit
#define TIMER_MOD_UP_COUNT    (1U << 0)  // Up counting mode bit
#define TIMER_EVC_CLEAR_EVENT (1U << 0)  // Clear event counter bit


/**
 * @brief Initialize Timer driver
 * @param driver Pointer to Timer driver structure
 * @param base_addr Base address of Timer peripheral
 * @param system_clock System clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int timer_init(timer_driver_t *driver, uint32_t base_addr, uint32_t system_clock);

/**
 * @brief Configure timer prescaler
 * @param driver Pointer to Timer driver structure
 * @param prescaler Prescaler value (0 = no division, 1 = divide by 2, etc.)
 * @return 0 on success, -1 on error
 */
int timer_set_prescaler(timer_driver_t *driver, uint32_t prescaler);

/**
 * @brief Configure timer auto-reload value
 * @param driver Pointer to Timer driver structure
 * @param reload_value Auto-reload value
 * @return 0 on success, -1 on error
 */
int timer_set_auto_reload(timer_driver_t *driver, uint32_t reload_value);

/**
 * @brief Set timer counting mode
 * @param driver Pointer to Timer driver structure
 * @param mode Counting mode (up or down)
 * @return 0 on success, -1 on error
 */
int timer_set_mode(timer_driver_t *driver, timer_mode_t mode);

/**
 * @brief Enable timer
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_enable(timer_driver_t *driver);

/**
 * @brief Disable timer
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_disable(timer_driver_t *driver);

/**
 * @brief Clear timer counter
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_clear_counter(timer_driver_t *driver);

/**
 * @brief Get current counter value
 * @param driver Pointer to Timer driver structure
 * @return Current counter value, 0xFFFFFFFF on error
 */
uint32_t timer_get_counter(timer_driver_t *driver);

/**
 * @brief Get event counter value
 * @param driver Pointer to Timer driver structure
 * @return Event counter value, 0xFFFFFFFF on error
 */
uint32_t timer_get_event_count(timer_driver_t *driver);

/**
 * @brief Clear event counter
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_clear_event_counter(timer_driver_t *driver);

/**
 * @brief Check if timer is enabled
 * @param driver Pointer to Timer driver structure
 * @return 1 if enabled, 0 if disabled, -1 on error
 */
int timer_is_enabled(timer_driver_t *driver);


/**
 * @brief Configure timer for microsecond precision
 * @param driver Pointer to Timer driver structure
 * @param period_us Period in microseconds
 * @return 0 on success, -1 on error
 */
int timer_config_microseconds(timer_driver_t *driver, uint32_t period_us);

/**
 * @brief Configure timer for millisecond precision
 * @param driver Pointer to Timer driver structure
 * @param period_ms Period in milliseconds
 * @return 0 on success, -1 on error
 */
int timer_config_milliseconds(timer_driver_t *driver, uint32_t period_ms);

/**
 * @brief Configure timer for second precision
 * @param driver Pointer to Timer driver structure
 * @param period_s Period in seconds
 * @return 0 on success, -1 on error
 */
int timer_config_seconds(timer_driver_t *driver, uint32_t period_s);

/**
 * @brief Start timer with specified period in microseconds
 * @param driver Pointer to Timer driver structure
 * @param period_us Period in microseconds
 * @return 0 on success, -1 on error
 */
int timer_start_microseconds(timer_driver_t *driver, uint32_t period_us);

/**
 * @brief Start timer with specified period in milliseconds
 * @param driver Pointer to Timer driver structure
 * @param period_ms Period in milliseconds
 * @return 0 on success, -1 on error
 */
int timer_start_milliseconds(timer_driver_t *driver, uint32_t period_ms);

/**
 * @brief Start timer with specified period in seconds
 * @param driver Pointer to Timer driver structure
 * @param period_s Period in seconds
 * @return 0 on success, -1 on error
 */
int timer_start_seconds(timer_driver_t *driver, uint32_t period_s);

/**
 * @brief Stop timer
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_stop(timer_driver_t *driver);

/**
 * @brief Reset timer (clear counter and event counter)
 * @param driver Pointer to Timer driver structure
 * @return 0 on success, -1 on error
 */
int timer_reset(timer_driver_t *driver);


/**
 * @brief Blocking delay using timer (microseconds)
 * @param driver Pointer to Timer driver structure
 * @param delay_us Delay in microseconds
 * @return 0 on success, -1 on error
 */
int timer_delay_us(timer_driver_t *driver, uint32_t delay_us);

/**
 * @brief Blocking delay using timer (milliseconds)
 * @param driver Pointer to Timer driver structure
 * @param delay_ms Delay in milliseconds
 * @return 0 on success, -1 on error
 */
int timer_delay_ms(timer_driver_t *driver, uint32_t delay_ms);

/**
 * @brief Non-blocking delay check (microseconds)
 * @param driver Pointer to Timer driver structure
 * @param delay_us Delay in microseconds
 * @return 1 if delay completed, 0 if still waiting, -1 on error
 */
int timer_delay_us_nonblocking(timer_driver_t *driver, uint32_t delay_us);

/**
 * @brief Non-blocking delay check (milliseconds)
 * @param driver Pointer to Timer driver structure
 * @param delay_ms Delay in milliseconds
 * @return 1 if delay completed, 0 if still waiting, -1 on error
 */
int timer_delay_ms_nonblocking(timer_driver_t *driver, uint32_t delay_ms);

#define TIMER_US_TO_TICKS(us, clk_hz)    ((us) * ((clk_hz) / 1000000UL))
#define TIMER_MS_TO_TICKS(ms, clk_hz)    ((ms) * ((clk_hz) / 1000UL))
#define TIMER_S_TO_TICKS(s, clk_hz)      ((s) * (clk_hz))

#define TIMER_TICKS_TO_US(ticks, clk_hz) ((ticks) / ((clk_hz) / 1000000UL))
#define TIMER_TICKS_TO_MS(ticks, clk_hz) ((ticks) / ((clk_hz) / 1000UL))
#define TIMER_TICKS_TO_S(ticks, clk_hz)  ((ticks) / (clk_hz))

#endif // __TIMER_DRIVER_H__