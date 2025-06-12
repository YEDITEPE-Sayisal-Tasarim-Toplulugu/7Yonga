#ifndef __TIMER_H__
#define __TIMER_H__

#include "string.h"
#include <stdint.h>

typedef uint32_t TIME_F;

typedef struct sTimerDriver
{
    uint32_t mtime;
    uint32_t mtimeh;
    uint32_t mtimecmp;
    uint32_t mtimecmph;
    uint32_t timerDivider;
    uint32_t timerValue;
} timerDriver;

//-----------------------------------------------------------------
// Prototypes
//-----------------------------------------------------------------
void timer_initial(int32_t base_addr, uint32_t clk_freq);

void set_time(TIME_F time);
void set_timeh(TIME_F time);
TIME_F get_time(void);
TIME_F get_timeh(void);

void set_timecmp(TIME_F time);
void set_timecmph(TIME_F time);
TIME_F get_timecmp(void);
TIME_F get_timecmph(void);

/////////////////////////////////////////
// timer
void set_timer_divider(uint32_t div);
void set_timer_value(uint32_t val);
uint32_t get_timer_divider( void );
uint32_t get_timer_value( void );


void delay(TIME_F time_ms);

#endif //__TIMER_H__