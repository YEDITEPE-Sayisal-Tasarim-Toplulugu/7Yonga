#include <stdint.h>

#include "qspi_flash_controller.h"

qspi_driver_t qspi_driver;
QSPI_RESID_TYPE resid;

#define QSPI_BASE_ADDR                              0x10020000
#define SYSTEM_CLOCK                                1000000*50
#define DEFAULT_QSPI_PRESCALER                      31

int main( void ) {
    QSPI_init(&qspi_driver, QSPI_BASE_ADDR, SYSTEM_CLOCK, DEFAULT_QSPI_PRESCALER);
    QSPI_read_RES(&qspi_driver, &resid);

    return 0;
}