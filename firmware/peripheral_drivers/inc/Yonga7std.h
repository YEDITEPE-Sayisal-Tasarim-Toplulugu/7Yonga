#ifndef __YONGA7STD__H__
#define __YONGA7STD__H__

#include "flash_controller.h"
#include "qspi_controller.h"
#include "gpio_driver.h"
#include "string.h"
#include "uart_driver.h"

#define YONGA7_SOC_PERIPHERAL_FREQUENCY                     (1000000 * 50)
#define YONGA7_IMEM_SIZE                                    (8*1024)
#define YONGA7_DMEM_SIZE                                    (8*1024)
#define YONGA7_UART_BASE                                    0x10010000
#define YONGA7_QSPI_BASE                                    0x10020000

#endif // __YONGA7STD__H__