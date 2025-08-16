#include "qspi_flash_controller.h"

#include <stdint.h>

int QSPI_init(qspi_driver_t *driver, uint32_t base_addr, uint32_t system_clock, uint8_t prescaler) {
    driver->base_addr = base_addr;
    driver->regs = (qspi_regs_t *)(base_addr);
    driver->system_clock = system_clock;
    driver->prescaler = prescaler;

    return 0;
}

int QSPI_set_prescaler(qspi_driver_t *driver, uint8_t prescaler) {
    driver->prescaler = prescaler;
    return 0;
}



int QSPI_read_RES(qspi_driver_t *driver, QSPI_RESID_TYPE *res_type) {
    QSPI_COMMAND cmd;
    uint32_t ret_data;

    cmd.instruction         = FLASH_ReadIdentification;
    cmd.data_mode           = QSPI_DATA_MODE_1X;
    cmd.data_direction      = QSPI_OP_READ;
    cmd.dummy_cycle_count   = 0;
    cmd.data_size           = 1;
    cmd.addres              = 0;

    QSPI_send_command(driver, cmd);
    QSPI_wait_transaction(driver);
    QSPI_read_register(driver, &ret_data, 0);
    
    res_type->ManufactureID = (ret_data >> 0) & 0xFF;
    res_type->DeviceID      = (ret_data >> 8) & 0xFF;

    return 0;
}

int QSPI_send_command(qspi_driver_t *driver, QSPI_COMMAND cmd) {
    uint32_t ccr_data;
    uint32_t addr_data;
    ccr_data = 0;
    ccr_data += (cmd.instruction & QSPI_CCR_INST_MASK)          << QSPI_CCR_INST_SHIFT;
    ccr_data += (cmd.data_mode & QSPI_CCR_MODE_MASK)            << QSPI_CCR_MODE_SHIFT;
    ccr_data += (cmd.data_direction & QSPI_CCR_DIRECTION_MASK)  << QSPI_CCR_DIRECTION_SHIFT;
    ccr_data += (cmd.dummy_cycle_count & QSPI_CCR_DUMY_MASK)    << QSPI_CCR_DUMY_SHIFT;
    ccr_data += (cmd.data_size & QSPI_CCR_SIZE_MASK)            << QSPI_CCR_SIZE_SHIFT;
    ccr_data += (driver->prescaler & QSPI_CCR_PRESCALER_MASK)   << QSPI_CCR_PRESCALER_SHIFT;
    ccr_data += (0 & QSPI_CCR_STA_MASK)                         << QSPI_CCR_STA_SHIFT;

    addr_data = (cmd.addres & QSPI_ADR_DATA_MASK)               << QSPI_ADR_DATA_SHIFT;

    QSPI_send_ADR(driver, addr_data);
    QSPI_send_CCR(driver, ccr_data);

    return 0;
}

int QSPI_wait_transaction(qspi_driver_t *driver) {
    while (driver->regs->STA & 0x1) ;
    return 0;
};

int QSPI_read_register(qspi_driver_t *driver, QSPI_REGISTER_DATA_TYPE *data, int i) {
    if ((i < 0) || (7 < i)) return -1;
    else {
        *data = *(((QSPI_REGISTER_DATA_TYPE *)(driver->regs->DR0) + i));
        return 0;
    }
}

int QSPI_send_CCR(qspi_driver_t *driver, uint32_t ccr_data) {
    driver->regs->CCR = ccr_data;
    return 0;
}

int QSPI_send_ADR(qspi_driver_t *driver, uint32_t adr_data) {
    driver->regs->ADR = adr_data;
    return 0;
}
