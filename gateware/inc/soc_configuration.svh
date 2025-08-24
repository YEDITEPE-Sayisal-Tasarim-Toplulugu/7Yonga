


`ifndef __SOC_CINFIGURATION_SVH__
`define __SOC_CINFIGURATION_SVH__

package soc_config_pkg;

typedef enum int { BYPASS, VIVADOBUF } CLOCK_GATE_TYPE;

// Parametrik sabitler
`ifdef VERILATOR_SIM
parameter int USE_SOFT_MEMORY_MODULES           = 1;
parameter int USE_SOFT_ROM_MODULES              = 1;
parameter int USE_BRAM_MEMORY_MODULES           = 0;
parameter CLOCK_GATE_TYPE USE_CLOCK_GATE_TYPE   = BYPASS;
parameter UART_PROGRAMMER_EXISTS                = 1;
`else
parameter int USE_SOFT_MEMORY_MODULES           = 1;
parameter int USE_SOFT_ROM_MODULES              = 1;
parameter int USE_BRAM_MEMORY_MODULES           = 0;
parameter CLOCK_GATE_TYPE USE_CLOCK_GATE_TYPE   = VIVADOBUF;
parameter UART_PROGRAMMER_EXISTS                = 1;
`endif

parameter UART_PROGRAMMER_BAUDE_RATE            = 9600;

// SOC
parameter int SOC_FREQUENCY_HZ                  = 1_000_000*50;     // 50MHz

// CORE
parameter int CORE_BOOT_ADDR                    = 32'h0000_0000;
parameter int CORE_MTVEC_ADDR                   = CORE_BOOT_ADDR;
parameter int CORE_DM_HALT_ADDR                 = CORE_BOOT_ADDR;
parameter int CORE_HART_ID                      = 32'd0;
parameter int CORE_DM_EXCEPTION_ADDR            = CORE_BOOT_ADDR;

parameter int CORE_CONF_COREV_PULP              = 0;
parameter int CORE_CONF_COREV_CLUSTER           = 0;
parameter int CORE_CONF_FPU                     = 0;
parameter int CORE_CONF_FPU_ADDMUL_LAT          = 0;
parameter int CORE_CONF_FPU_OTHERS_LAT          = 0;
parameter int CORE_CONF_ZFINX                   = 0;
parameter int CORE_CONF_NUM_MHPMCOUNTERS        = 1;

// AXI4 
parameter int AXI4_CONF_ADDR_WIDTH              = 32'd32;
parameter int AXI4_CONF_DATA_WIDTH              = 32'd32;
parameter int AXI4_CONF_ID_WIDTH                = 32'd8;
parameter int AXI4_CONF_USER_WIDTH              = 32'd8;

// AXI4-Lite    
parameter int AXI4L_CONF_ADDR_WIDTH              = 32'd32;
parameter int AXI4L_CONF_DATA_WIDTH              = 32'd32;
parameter int AXI4L_CONF_ID_WIDTH                = 32'd8;
parameter int AXI4L_CONF_USER_WIDTH              = 32'd8;

endpackage

`endif // __SOC_CINFIGURATION_SVH__
