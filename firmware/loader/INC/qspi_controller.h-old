
#ifndef __QSPI_CONTROLLER_H__
#define __QSPI_CONTROLLER_H__

#include <stdint.h>

#define QSPI_REGISTER_DATA_TYPE                 uint32_t
#define BYTE_INDEX_2_REG_ADDR(i)                ((i) / sizeof(QSPI_REGISTER_DATA_TYPE))
#define BYTE_INDEX_2_REG_SHIFT(i)               (((i) % sizeof(QSPI_REGISTER_DATA_TYPE))*8)
#define QSPI_REGISTER_WRITE_BYTE(o, b, i)                                      \
    ( ((o) & ~(0xFFu << BYTE_INDEX_2_REG_SHIFT(i))) |                          \
      (((uint32_t)(b) & 0xFFu) << BYTE_INDEX_2_REG_SHIFT(i)) )
#define QSPI_REGISTER_READ_BYTE(o, i) \
    ( (uint8_t)(((o) >> BYTE_INDEX_2_REG_SHIFT(i)) & 0xFFu) )

typedef struct {
    volatile uint32_t CCR;    // 0x00 - Communication configuration register
    volatile uint32_t ADR;    // 0x04 - Address register
    volatile uint32_t DR0;    // 0x08 - Data register 0
    volatile uint32_t DR1;    // 0x0C - Data register 1
    volatile uint32_t DR2;    // 0x10 - Data register 2
    volatile uint32_t DR3;    // 0x14 - Data register 3
    volatile uint32_t DR4;    // 0x18 - Data register 4
    volatile uint32_t DR5;    // 0x1C - Data register 5
    volatile uint32_t DR6;    // 0x20 - Data register 6
    volatile uint32_t DR7;    // 0x24 - Data register 7
    volatile uint32_t STA;    // 0x28 - Status register
} qspi_regs_t;

typedef struct {
    uint32_t base_addr;       // Base address of QSPI peripheral
    qspi_regs_t *regs;        // Pointer to QSPI registers
    uint32_t system_clock;    // System clock frequency in Hz
    uint32_t prescaler;
} qspi_driver_t;

typedef enum {
    QSPI_DATA_MODE_NONE = 0,  // No data phase
    QSPI_DATA_MODE_1X   = 1,  // x1 mode (single line)
    QSPI_DATA_MODE_2X   = 2,  // x2 mode (dual line)
    QSPI_DATA_MODE_4X   = 3   // x4 mode (quad line)
} qspi_data_mode_t;

typedef enum {
    QSPI_OP_READ  = 0,        // Read operation
    QSPI_OP_WRITE = 1         // Write operation
} qspi_operation_t;

typedef struct
{
    uint8_t             instruction;
    qspi_data_mode_t    data_mode;
    qspi_operation_t    data_direction;
    uint32_t            data_size;
    uint32_t            dummy_cycle_count;
    uint32_t            address;
} QSPI_COMMAND;

#define QSPI_STA_COMPLETE    (1U << 0)  // Transaction complete
#define QSPI_STA_BUSY        (1U << 1)  // QSPI busy

#define QSPI_PAGE_SIZE           256
#define QSPI_SECTOR_SIZE         4096
#define QSPI_MAX_ADDRESS         0xFFFFFF  // 24-bit addressing

#define QSPI_ADDRESS_TO_PAGE(addr)    ((addr) / QSPI_PAGE_SIZE)
#define QSPI_ADDRESS_TO_SECTOR(addr)  ((addr) / QSPI_SECTOR_SIZE)
#define QSPI_IS_PAGE_ALIGNED(addr)    (((addr) % QSPI_PAGE_SIZE) == 0)
#define QSPI_IS_SECTOR_ALIGNED(addr)  (((addr) % QSPI_SECTOR_SIZE) == 0)

// Default timeouts
#define QSPI_TIMEOUT_DEFAULT     1000   // 1 second
#define QSPI_TIMEOUT_ERASE       10000  // 10 seconds for sector erase

#define QSPI_CCR_INST_MASK          0xFF
#define QSPI_CCR_INST_SHIFT         0
#define QSPI_CCR_MODE_MASK          0x03
#define QSPI_CCR_MODE_SHIFT         8
#define QSPI_CCR_DIRECTION_MASK     0x01
#define QSPI_CCR_DIRECTION_SHIFT    10
#define QSPI_CCR_DUMY_MASK          0x1F
#define QSPI_CCR_DUMY_SHIFT         11
#define QSPI_CCR_SIZE_MASK          0x1FF
#define QSPI_CCR_SIZE_SHIFT         16
#define QSPI_CCR_PRESCALER_MASK     0x3F
#define QSPI_CCR_PRESCALER_SHIFT    25
#define QSPI_CCR_STA_MASK           0x01
#define QSPI_CCR_STA_SHIFT          31

#define QSPI_ADR_DATA_MASK          QSPI_MAX_ADDRESS
#define QSPI_ADR_DATA_SHIFT         0

/**
 * @brief Initialize QSPI driver
 * @param driver Pointer to QSPI driver structure
 * @param base_addr Base address of QSPI peripheral
 * @param system_clock System clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int QSPI_init(qspi_driver_t *driver, uint32_t base_addr, uint32_t system_clock, uint32_t prescaler);

/**
 * @brief Set QSPI clock prescaler
 * @param driver Pointer to QSPI driver structure
 * @param prescaler Prescaler value (0 = no division, 1 = divide by 2, etc.)
 * @return 0 on success, -1 on error
 */
int QSPI_set_prescaler(qspi_driver_t *driver, uint32_t prescaler);

// WRDI (Write Disable), WREN (Write Enable), CLSR (Clear Status Register-1), RESET (Software Reset), 
int QSPI_send_single_instruction(qspi_driver_t *driver, uint8_t inst);
// WRR (Write Register – Status-1, Configuration-1) 
int QSPI_send_instruction_and_bytes(qspi_driver_t *driver, uint8_t inst, uint8_t arr[], int size);
int QSPI_send_command(qspi_driver_t *driver, QSPI_COMMAND cmd);
int QSPI_wait_transaction(qspi_driver_t *driver);
int QSPI_write_register_inbyte(qspi_driver_t *driver, uint8_t data, int index);
uint8_t QSPI_read_register_inbyte(qspi_driver_t *driver, int index);
int QSPI_read_register(qspi_driver_t *driver, QSPI_REGISTER_DATA_TYPE *data, int i);
int QSPI_send_CCR(qspi_driver_t *driver, uint32_t ccr_data);
int QSPI_send_ADR(qspi_driver_t *driver, uint32_t adr_data);

#endif // __QSPI_CONTROLLER_H__
