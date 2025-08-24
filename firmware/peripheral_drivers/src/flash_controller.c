#include "flash_controller.h"

#include <stdint.h>
#include "qspi_controller.h"

volatile uint8_t FLASH_status_register_value;
volatile uint8_t FLASH_configure_register_value;

int FLASH_read_REMS(qspi_driver_t *driver, FLASH_RDID_DATA *res_type) {
    uint8_t data[2];

    FLASH_read_register(driver, data, FLASH_ReadIdentification_REMS, 2);

    res_type->ManufactureID = data[0];
    res_type->DeviceID      = data[1];
    
    return 0;
}

uint8_t FLASH_read_RES(qspi_driver_t *driver, FLASH_RDID_DATA *res_type) {
    uint8_t res_data;
    FLASH_read_register_command(driver, &res_data, FLASH_ReadElectronicSignature_RES, 3, 1);
    return res_data;
}

int FLASH_write_enable(qspi_driver_t *driver) {
    QSPI_send_single_instruction(driver, FLASH_WriteEnable_WREN);
    return 0;
}

int FLASH_write_disable(qspi_driver_t *driver) {
    QSPI_send_single_instruction(driver, FLASH_WriteDisable_WRDI);
    return 0;
}

int FLASH_clear_status_register(qspi_driver_t *driver) {
    QSPI_send_single_instruction(driver, FLASH_ClearStatusRegister_CLSR);
    return 0;
}
int FLASH_software_reset(qspi_driver_t *driver) {
    QSPI_send_single_instruction(driver, FLASH_SoftwareReset_RESET);
    return 0;
}

uint8_t FLASH_read_status_reg1(qspi_driver_t *driver) {
    uint8_t data;
    FLASH_read_register(driver, &data, FLASH_ReadStatusRegister_1_RDSR1, 1);
    FLASH_status_register_value = data;
    return FLASH_status_register_value;
}

uint8_t FLASH_read_status_reg2(qspi_driver_t *driver) {
    uint8_t data;
    FLASH_read_register(driver, &data, FLASH_ReadStatusRegister_2_RDSR2, 1);
    return data;
}

uint8_t FLASH_read_configure_reg(qspi_driver_t *driver) {
    uint8_t data;
    FLASH_read_register(driver, &data, FLASH_ReadConfigurationRegister_RDCR, 1);
    FLASH_configure_register_value = data;
    return FLASH_configure_register_value;
}

int FLASH_read_register(qspi_driver_t *driver, uint8_t *buffer, uint8_t inst, int data_size) {
    return FLASH_read_register_command(driver, buffer, inst, 0, data_size);
}

int FLASH_read_register_command(qspi_driver_t *driver, uint8_t *buffer, uint8_t inst, int dummyCount, int data_size) {
    QSPI_COMMAND cmd;

    cmd.instruction         = inst;
    cmd.data_mode           = QSPI_DATA_MODE_1X;
    cmd.data_direction      = QSPI_OP_READ;
    cmd.dummy_cycle_count   = dummyCount;
    cmd.data_size           = data_size;
    cmd.address             = 0;

    QSPI_send_command(driver, cmd);
    QSPI_wait_transaction(driver);
    
    for (int i=0; i<data_size; i++) {
        *buffer++ = QSPI_read_register_inbyte(driver, i);
    }

    return data_size;
}

int FLASH_update_status_and_confg_regs(qspi_driver_t *driver) {
    FLASH_write_enable(driver);
    QSPI_wait_transaction(driver);

    QSPI_COMMAND cmd;

    cmd.instruction         = FLASH_WriteRegisters_WRR;
    cmd.data_mode           = QSPI_DATA_MODE_1X;
    cmd.data_direction      = QSPI_OP_WRITE;
    cmd.dummy_cycle_count   = 0;
    cmd.data_size           = 2;
    cmd.address             = 0;

    QSPI_write_register_inbyte(driver, FLASH_status_register_value, 0);
    QSPI_write_register_inbyte(driver, FLASH_configure_register_value, 1);

    QSPI_send_command(driver, cmd);
    QSPI_wait_transaction(driver);
    
    while (1) {
        FLASH_status_register_value = FLASH_read_status_reg1(driver);

        if (!((FLASH_status_register_value >> FLASH_STATUS_REGISTER_WIP_INDEX) & 0x1)) break;
    }

    if (((FLASH_status_register_value >> FLASH_STATUS_REGISTER_P_ERR_INDEX) & 0x1)) return -1;
    if (((FLASH_status_register_value >> FLASH_STATUS_REGISTER_E_ERR_INDEX) & 0x1)) return -2;

    return 0;
}

int FLASH_switch_QUAD_mode(qspi_driver_t *driver) {
    int ret = -3;
    FLASH_configure_register_value |= (1<<FLASH_CONFIGURE_REGISTER_QUAD_INDEX);
    ret = FLASH_update_status_and_confg_regs(driver);
    return ret;
}

int FLASH_switch_SINGLE_DOUBLE_mode(qspi_driver_t *driver) {
    int ret = -3;
    FLASH_configure_register_value &= ~(1<<FLASH_CONFIGURE_REGISTER_QUAD_INDEX);
    ret = FLASH_update_status_and_confg_regs(driver);
    return ret;
}
