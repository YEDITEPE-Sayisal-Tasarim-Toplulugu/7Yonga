#include "timer.h"
#include <stdint.h>

static volatile timerDriver *timer_driver;
static volatile uint32_t clock_khz;

void timer_initial(int32_t base_addr, uint32_t clk_freq_khz)
{
    timer_driver = (timerDriver*)base_addr;
    clock_khz = clk_freq_khz;
}

/////////////////////////////////////////
// mtime
void set_time(TIME_F time)
{
    timer_driver->mtime = time;
}

void set_timeh(TIME_F time)
{
    timer_driver->mtimeh = time;
}

TIME_F get_time(void)
{
    return timer_driver->mtime;
}

TIME_F get_timeh(void)
{
    return timer_driver->mtimeh;
}

/////////////////////////////////////////
// mtimecmp
void set_timecmp(TIME_F time)
{
    timer_driver->mtimecmp = time;
}

void set_timecmph(TIME_F time)
{
    timer_driver->mtimecmph = time;
}

TIME_F get_timecmp(void)
{
    return timer_driver->mtimecmp;
}

TIME_F get_timecmph(void)
{
    return timer_driver->mtimecmph;
}

/////////////////////////////////////////
// timer
void set_timer_divider(uint32_t div) {
    timer_driver->timerDivider = div;
}

void set_timer_value(uint32_t val) {
    timer_driver->timerValue = val;
}

uint32_t get_timer_divider( void ) {
    return timer_driver->timerDivider;
}

uint32_t get_timer_value( void ) {
    return timer_driver->timerValue;
}

void delay(TIME_F time_ms)
{
    TIME_F time1;
    
    set_time(0);
    set_timeh(0);

    time1 = get_time();

    uint32_t tick = time_ms * clock_khz;

    while ((get_time() - time1) < tick)
        ;
}