#include <stdint.h>
#include "csr.h"
#include "stdio.h"
#include "string.h"
#include "uart.h"
#include "timer.h"
#include "random.h"

#define UART_BAUDE_RATE 115200
#define UART_BASE_ADDR 0x20000000
#define TIMER_BASE_ADDR 0x30000000

int readCharUART()
{
	return read_char(1);
}

int core_init (void) {
    uart_initial(UART_BASE_ADDR, (((CLOCK_FREQ * 1000000) / UART_BAUDE_RATE)- 1));
    timer_initial(TIMER_BASE_ADDR, (CLOCK_FREQ*1000)); // 1ms each tick
	printf_init(send_char, readCharUART);
	

	set_timer_divider((CLOCK_FREQ * 1000000) / 1000);

    srand(csr_read(time));

    return 0;
}