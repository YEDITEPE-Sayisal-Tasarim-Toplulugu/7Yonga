#ifndef __QSPI_DRIVER_H__
#define __QSPI_DRIVER_H__

#include <stdint.h>

#define QSPI_CCR_OFFSET    0x00    // Communication configuration register
#define QSPI_ADR_OFFSET    0x04    // Address register
#define QSPI_DR0_OFFSET    0x08    // Data register 0
#define QSPI_DR1_OFFSET    0x0C    // Data register 1
#define QSPI_DR2_OFFSET    0x10    // Data register 2
#define QSPI_DR3_OFFSET    0x14    // Data register 3
#define QSPI_DR4_OFFSET    0x18    // Data register 4
#define QSPI_DR5_OFFSET    0x1C    // Data register 5
#define QSPI_DR6_OFFSET    0x20    // Data register 6
#define QSPI_DR7_OFFSET    0x24    // Data register 7
#define QSPI_STA_OFFSET    0x28    // Status register

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
} qspi_driver_t;

#define QSPI_CCR_INSTRUCTION_MASK    0x000000FF  // [7:0]
#define QSPI_CCR_DATA_MODE_MASK      0x00000300  // [9:8]
#define QSPI_CCR_DATA_MODE_SHIFT     8
#define QSPI_CCR_READ_WRITE_MASK     0x00000400  // [10]
#define QSPI_CCR_READ_WRITE_SHIFT    10
#define QSPI_CCR_DUMMY_CYCLES_MASK   0x0000F800  // [15:11]
#define QSPI_CCR_DUMMY_CYCLES_SHIFT  11
#define QSPI_CCR_DATA_LENGTH_MASK    0x01FF0000  // [24:16]
#define QSPI_CCR_DATA_LENGTH_SHIFT   16
#define QSPI_CCR_PRESCALER_MASK      0x7E000000  // [30:25]
#define QSPI_CCR_PRESCALER_SHIFT     25
#define QSPI_CCR_CLEAR_STATUS        0x80000000  // [31]

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

#define QSPI_STA_COMPLETE    (1U << 0)  // Transaction complete
#define QSPI_STA_BUSY        (1U << 1)  // QSPI busy

#define QSPI_CMD_READ             0x03  // Read data
#define QSPI_CMD_DOR              0x3B  // Read dual out
#define QSPI_CMD_QOR              0x6B  // Read quad out
#define QSPI_CMD_PP               0x02  // Page program
#define QSPI_CMD_QPP              0x32  // Quad page program
#define QSPI_CMD_SE               0x20  // Sector erase (4KB)
#define QSPI_CMD_READ_ID          0x90  // Read electronic manufacturer signature
#define QSPI_CMD_RDID             0x9F  // Read JEDEC ID
#define QSPI_CMD_RES              0xAB  // Read electronic signature
#define QSPI_CMD_RDSR1            0x05  // Read status register 1
#define QSPI_CMD_RDSR2            0x35  // Read status register 2
#define QSPI_CMD_RDCR             0x15  // Read configuration register
#define QSPI_CMD_WRR              0x01  // Write register
#define QSPI_CMD_WRDI             0x04  // Write disable
#define QSPI_CMD_WREN             0x06  // Write enable
#define QSPI_CMD_CLSR             0x30  // Clear status register
#define QSPI_CMD_RESET            0xF0  // Software reset

#define FLASH_SR1_WIP             (1U << 0)  // Write in progress
#define FLASH_SR1_WEL             (1U << 1)  // Write enable latch
#define FLASH_SR1_BP0             (1U << 2)  // Block protect 0
#define FLASH_SR1_BP1             (1U << 3)  // Block protect 1
#define FLASH_SR1_BP2             (1U << 4)  // Block protect 2
#define FLASH_SR1_TB              (1U << 5)  // Top/bottom protect
#define FLASH_SR1_SEC             (1U << 6)  // Sector protect
#define FLASH_SR1_SRP0            (1U << 7)  // Status register protect 0


/**
 * @brief Initialize QSPI driver
 * @param driver Pointer to QSPI driver structure
 * @param base_addr Base address of QSPI peripheral
 * @param system_clock System clock frequency in Hz
 * @return 0 on success, -1 on error
 */
int qspi_init(qspi_driver_t *driver, uint32_t base_addr, uint32_t system_clock);

/**
 * @brief Set QSPI clock prescaler
 * @param driver Pointer to QSPI driver structure
 * @param prescaler Prescaler value (0 = no division, 1 = divide by 2, etc.)
 * @return 0 on success, -1 on error
 */
int qspi_set_prescaler(qspi_driver_t *driver, uint8_t prescaler);

/**
 * @brief Wait for QSPI operation to complete
 * @param driver Pointer to QSPI driver structure
 * @param timeout_ms Timeout in milliseconds (0 = no timeout)
 * @return 0 on success, -1 on timeout/error
 */
int qspi_wait_complete(qspi_driver_t *driver, uint32_t timeout_ms);

/**
 * @brief Check if QSPI is busy
 * @param driver Pointer to QSPI driver structure
 * @return 1 if busy, 0 if idle, -1 on error
 */
int qspi_is_busy(qspi_driver_t *driver);

/**
 * @brief Clear status flags
 * @param driver Pointer to QSPI driver structure
 * @return 0 on success, -1 on error
 */
int qspi_clear_status(qspi_driver_t *driver);

/**
 * @brief Execute command without data phase
 * @param driver Pointer to QSPI driver structure
 * @param command Command byte to send
 * @return 0 on success, -1 on error
 */
int qspi_command_only(qspi_driver_t *driver, uint8_t command);

/**
 * @brief Execute command with address phase
 * @param driver Pointer to QSPI driver structure
 * @param command Command byte to send
 * @param address 24-bit address
 * @return 0 on success, -1 on error
 */
int qspi_command_address(qspi_driver_t *driver, uint8_t command, uint32_t address);

/**
 * @brief Execute read command
 * @param driver Pointer to QSPI driver structure
 * @param command Command byte
 * @param address 24-bit address (0 if no address phase)
 * @param dummy_cycles Number of dummy cycles
 * @param data_mode Data phase mode (x1, x2, x4)
 * @param data Buffer to store read data
 * @param length Number of bytes to read (1-256)
 * @return Number of bytes read, -1 on error
 */
int qspi_read_data(qspi_driver_t *driver, uint8_t command, uint32_t address, 
                   uint8_t dummy_cycles, qspi_data_mode_t data_mode,
                   uint8_t *data, uint16_t length);

/**
 * @brief Execute write command
 * @param driver Pointer to QSPI driver structure
 * @param command Command byte
 * @param address 24-bit address (0 if no address phase)
 * @param data_mode Data phase mode (x1, x2, x4)
 * @param data Buffer containing data to write
 * @param length Number of bytes to write (1-256)
 * @return Number of bytes written, -1 on error
 */
int qspi_write_data(qspi_driver_t *driver, uint8_t command, uint32_t address,qspi_data_mode_t data_mode, const uint8_t *data, uint16_t length);

/**
 * @brief Read flash JEDEC ID
 * @param driver Pointer to QSPI driver structure
 * @param manufacturer_id Pointer to store manufacturer ID
 * @param device_id Pointer to store device ID (16-bit)
 * @return 0 on success, -1 on error
 */
int qspi_flash_read_id(qspi_driver_t *driver, uint8_t *manufacturer_id, uint16_t *device_id);

/**
 * @brief Read flash status register
 * @param driver Pointer to QSPI driver structure
 * @param status Pointer to store status register value
 * @return 0 on success, -1 on error
 */
int qspi_flash_read_status(qspi_driver_t *driver, uint8_t *status);

/**
 * @brief Enable flash write operations
 * @param driver Pointer to QSPI driver structure
 * @return 0 on success, -1 on error
 */
int qspi_flash_write_enable(qspi_driver_t *driver);

/**
 * @brief Disable flash write operations
 * @param driver Pointer to QSPI driver structure
 * @return 0 on success, -1 on error
 */
int qspi_flash_write_disable(qspi_driver_t *driver);

/**
 * @brief Wait for flash write/erase completion
 * @param driver Pointer to QSPI driver structure
 * @param timeout_ms Timeout in milliseconds
 * @return 0 on success, -1 on timeout/error
 */
int qspi_flash_wait_ready(qspi_driver_t *driver, uint32_t timeout_ms);

/**
 * @brief Read data from flash memory
 * @param driver Pointer to QSPI driver structure
 * @param address Start address to read from
 * @param data Buffer to store read data
 * @param length Number of bytes to read
 * @param data_mode Data transfer mode (x1, x2, x4)
 * @return Number of bytes read, -1 on error
 */
int qspi_flash_read(qspi_driver_t *driver, uint32_t address, uint8_t *data, uint16_t length, qspi_data_mode_t data_mode);

/**
 * @brief Program a page in flash memory
 * @param driver Pointer to QSPI driver structure
 * @param address Start address to program (must be page-aligned)
 * @param data Data to program
 * @param length Number of bytes to program (1-256)
 * @param data_mode Data transfer mode (x1, x4 for QPP)
 * @return Number of bytes programmed, -1 on error
 */
int qspi_flash_page_program(qspi_driver_t *driver, uint32_t address, const uint8_t *data, uint16_t length, qspi_data_mode_t data_mode);

/**
 * @brief Erase a sector in flash memory
 * @param driver Pointer to QSPI driver structure
 * @param address Address within sector to erase (4KB sectors)
 * @return 0 on success, -1 on error
 */
int qspi_flash_sector_erase(qspi_driver_t *driver, uint32_t address);

/**
 * @brief Reset flash memory
 * @param driver Pointer to QSPI driver structure
 * @return 0 on success, -1 on error
 */
int qspi_flash_reset(qspi_driver_t *driver);

/**
 * @brief Initialize flash memory
 * @param driver Pointer to QSPI driver structure
 * @return 0 on success, -1 on error
 */
int qspi_flash_init(qspi_driver_t *driver);

/**
 * @brief Write data to flash with automatic page boundary handling
 * @param driver Pointer to QSPI driver structure
 * @param address Start address
 * @param data Data to write
 * @param length Number of bytes to write
 * @return Number of bytes written, -1 on error
 */
int qspi_flash_write(qspi_driver_t *driver, uint32_t address, 
                     const uint8_t *data, uint32_t length);

/**
 * @brief Erase and write data to flash
 * @param driver Pointer to QSPI driver structure
 * @param address Start address (should be sector-aligned for best performance)
 * @param data Data to write
 * @param length Number of bytes to write
 * @return Number of bytes written, -1 on error
 */
int qspi_flash_erase_write(qspi_driver_t *driver, uint32_t address,const uint8_t *data, uint32_t length);

/**
 * @brief Load program from flash to memory
 * @param driver Pointer to QSPI driver structure
 * @param flash_addr Flash address to read from
 * @param mem_addr Memory address to write to
 * @param length Number of bytes to copy
 * @return Number of bytes copied, -1 on error
 */
int qspi_boot_load_program(qspi_driver_t *driver, uint32_t flash_addr, uint32_t mem_addr, uint32_t length);

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

#endif // __QSPI_DRIVER_H__