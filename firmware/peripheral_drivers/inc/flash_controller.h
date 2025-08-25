#ifndef __FLASH_CONTROLLER_H__
#define __FLASH_CONTROLLER_H__

#include <stdint.h>
#include "qspi_controller.h"

#define FLASH_ReadIdentification_REMS               0x90
#define FLASH_ReadIdentification_RDID               0x9F
#define FLASH_ReadElectronicSignature_RES           0xAB
#define FLASH_WriteEnable_WREN                      0x06
#define FLASH_WriteDisable_WRDI                     0x04
#define FLASH_ClearStatusRegister_CLSR              0x30
#define FLASH_SoftwareReset_RESET                   0xF0
#define FLASH_ReadStatusRegister_1_RDSR1            0x05
#define FLASH_ReadStatusRegister_2_RDSR2            0x07
#define FLASH_ReadConfigurationRegister_RDCR        0x35
#define FLASH_WriteRegisters_WRR                    0x01

#define FLASH_STATUS_REGISTER_SRWD_INDEX            7
#define FLASH_STATUS_REGISTER_P_ERR_INDEX           6
#define FLASH_STATUS_REGISTER_E_ERR_INDEX           5
#define FLASH_STATUS_REGISTER_BP2_INDEX             4
#define FLASH_STATUS_REGISTER_BP1_INDEX             3
#define FLASH_STATUS_REGISTER_BP0_INDEX             2
#define FLASH_STATUS_REGISTER_WEL_INDEX             1
#define FLASH_STATUS_REGISTER_WIP_INDEX             0

#define FLASH_CONFIGURE_REGISTER_LC1_INDEX          7
#define FLASH_CONFIGURE_REGISTER_LC0_INDEX          6
#define FLASH_CONFIGURE_REGISTER_TBPROT_INDEX       5
#define FLASH_CONFIGURE_REGISTER_DNU_INDEX          4
#define FLASH_CONFIGURE_REGISTER_BPNV_INDEX         3
#define FLASH_CONFIGURE_REGISTER_TBPARM_INDEX       2
#define FLASH_CONFIGURE_REGISTER_QUAD_INDEX         1
#define FLASH_CONFIGURE_REGISTER_FREEZE_INDEX       0

typedef struct {
    uint8_t ManufactureID;
    uint8_t DeviceID;
} FLASH_RDID_DATA;

int FLASH_read_REMS(qspi_driver_t *driver, FLASH_RDID_DATA *res_type);
uint8_t FLASH_read_RES(qspi_driver_t *driver);
int FLASH_write_enable(qspi_driver_t *driver);
int FLASH_write_disable(qspi_driver_t *driver);
int FLASH_clear_status_register(qspi_driver_t *driver);
int FLASH_software_reset(qspi_driver_t *driver);
uint8_t FLASH_read_status_reg1(qspi_driver_t *driver);
uint8_t FLASH_read_status_reg2(qspi_driver_t *driver);
uint8_t FLASH_read_configure_reg(qspi_driver_t *driver);
int FLASH_read_register_with_addr(qspi_driver_t *driver, uint8_t *buffer, uint8_t inst, int addr, int data_size);
int FLASH_read_register(qspi_driver_t *driver, uint8_t *buffer, uint8_t inst, int data_size);
int FLASH_read_register_command(qspi_driver_t *driver, uint8_t *buffer, uint8_t inst, int addr, int dummyCount, int data_size);
int FLASH_update_status_and_confg_regs(qspi_driver_t *driver);
int FLASH_switch_QUAD_mode(qspi_driver_t *driver);
int FLASH_switch_SINGLE_DOUBLE_mode(qspi_driver_t *driver);

#endif