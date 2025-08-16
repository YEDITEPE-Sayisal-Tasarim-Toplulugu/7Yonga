`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.05.2025 19:12:45
// Design Name: 
// Module Name: soc_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`include "soc_configuration.svh"
`include "soc_addr_rules.svh"
`include "soc_interface_list.svh"

import soc_addr_rules_pkg::*;
import soc_config_pkg::*;
import axi_pkg::*;

module soc_top
    (
        input logic clk_i, reset_i,
        
        SOC_PERIPHERAL_INF.Slave    PERIPHERAL_INTF
    );
    
    localparam int unsigned SYSTEM_BUS_MASTER_COUNT     = 32'd1;
    localparam int unsigned SYSTEM_BUS_SLAVE_COUNT      = 32'd2;
    
    localparam int unsigned AXI4_MASTER_CORE_ID         = 32'd0;
    localparam int unsigned AXI4_SLAVE_INST_SRAM_ID     = 32'd0;
    localparam int unsigned AXI4_SLAVE_DATA_SRAM_ID     = 32'd1;
    localparam int unsigned AXI4_SLAVE_PERIPHERALS_ID   = 32'd2;
    
    logic [31:0] CORE_boot_addr_w           = soc_config_pkg::CORE_BOOT_ADDR;
    logic [31:0] CORE_mtvec_addr_w          = soc_config_pkg::CORE_MTVEC_ADDR;
    logic [31:0] CORE_dm_halt_addr_w        = soc_config_pkg::CORE_DM_HALT_ADDR;
    logic [31:0] CORE_hart_id_w             = soc_config_pkg::CORE_HART_ID;
    logic [31:0] CORE_dm_exception_addr_w   = soc_config_pkg::CORE_DM_EXCEPTION_ADDR;
    
    CORE_INST_INF CORE_instr_intf();
    CORE_DATA_INF CORE_data_intf();
    
    AXI_BUS #(
        .AXI_ADDR_WIDTH (   soc_config_pkg::AXI4_CONF_ADDR_WIDTH    ),
        .AXI_DATA_WIDTH (   soc_config_pkg::AXI4_CONF_DATA_WIDTH    ),
        .AXI_ID_WIDTH   (   soc_config_pkg::AXI4_CONF_ID_WIDTH      ),
        .AXI_USER_WIDTH (   soc_config_pkg::AXI4_CONF_USER_WIDTH    )
    ) AXI4_Slaves[SYSTEM_BUS_SLAVE_COUNT]();
    
    AXI_BUS #(
        .AXI_ADDR_WIDTH (   soc_config_pkg::AXI4_CONF_ADDR_WIDTH    ),
        .AXI_DATA_WIDTH (   soc_config_pkg::AXI4_CONF_DATA_WIDTH    ),
        .AXI_ID_WIDTH   (   soc_config_pkg::AXI4_CONF_ID_WIDTH      ),
        .AXI_USER_WIDTH (   soc_config_pkg::AXI4_CONF_USER_WIDTH    )
    ) AXI4_Masters[SYSTEM_BUS_MASTER_COUNT]();
    
    axi_pkg::xbar_rule_32_t [SYSTEM_BUS_SLAVE_COUNT-1:0] AXI4_AddrMap;
    
    assign AXI4_AddrMap[0] = {AXI4_SLAVE_INST_SRAM_ID, soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.start_addr, soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.end_addr};
    assign AXI4_AddrMap[1] = {AXI4_SLAVE_DATA_SRAM_ID, soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.start_addr, soc_addr_rules_pkg::DATA_SRAM_ADDR_RULE.end_addr};
    //assign AXI4_AddrMap[2] = {AXI4_SLAVE_PERIPHERALS_ID, soc_addr_rules_pkg::PERIPHERALS_TOP_ADDR_RULE.start_addr, soc_addr_rules_pkg::PERIPHERALS_TOP_ADDR_RULE.end_addr};
    
    ////////////////////////////////////////////////////////////////
    logic CORE_data_intf_data_rvalid_w, CORE_data_intf_data_gnt_w;
    logic core_data_intf_req_r, core_data_intf_we_r, core_data_intf_gnt_r;
    logic [3:0] core_data_intf_be_r;
    logic [soc_config_pkg::AXI4_CONF_ADDR_WIDTH-1:0] core_data_intf_addr_r;
    logic [soc_config_pkg::AXI4_CONF_DATA_WIDTH-1:0] core_data_intf_data_r;
    
    logic core_data_intf_req_w, core_data_intf_we_w, core_data_intf_gnt_w;
    logic [3:0] core_data_intf_be_w;
    logic [soc_config_pkg::AXI4_CONF_ADDR_WIDTH-1:0] core_data_intf_addr_w;
    logic [soc_config_pkg::AXI4_CONF_DATA_WIDTH-1:0] core_data_intf_data_w;
    
    always_ff @(posedge clk_i, posedge reset_i) begin
        if (reset_i) begin
            core_data_intf_req_r    <= 0;
            core_data_intf_we_r     <= 0;
            core_data_intf_be_r     <= 0;
            core_data_intf_addr_r   <= 0;
            core_data_intf_data_r   <= 0;
            core_data_intf_gnt_r    <= 0;
        end else begin
            if (core_data_intf_gnt_w & core_data_intf_req_w) begin
                core_data_intf_req_r    <= 1'b1;
                core_data_intf_we_r     <= core_data_intf_we_w;
                core_data_intf_be_r     <= core_data_intf_be_w;
                core_data_intf_addr_r   <= core_data_intf_addr_w;
                core_data_intf_data_r   <= core_data_intf_data_w;
                core_data_intf_gnt_r    <= 1'b0;
            end else if (CORE_data_intf_data_rvalid_w) begin
                core_data_intf_req_r    <= 1'b0;
            end
            
            if (core_data_intf_req_r & ~core_data_intf_gnt_r) begin
                core_data_intf_gnt_r <= CORE_data_intf_data_gnt_w;
            end
        end
    end
    
    assign CORE_data_intf_data_rvalid_w = CORE_data_intf.data_rvalid;
    assign CORE_data_intf_data_gnt_w    = CORE_data_intf.data_gnt;
    
    assign CORE_data_intf.data_req     = core_data_intf_req_r & ~core_data_intf_gnt_r;
    assign CORE_data_intf.data_we      = core_data_intf_we_r;
    assign CORE_data_intf.data_be      = core_data_intf_be_r;
    assign CORE_data_intf.data_addr    = core_data_intf_addr_r;
    assign CORE_data_intf.data_wdata   = core_data_intf_data_r;
    assign core_data_intf_gnt_w        = ~core_data_intf_req_r;
    
    ////////////////////////////////////////////////////////////////
    
    cv32e40p_top #(
        .COREV_PULP         (soc_config_pkg::CORE_CONF_COREV_PULP),  // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. cv.elw)
        .COREV_CLUSTER      (soc_config_pkg::CORE_CONF_COREV_CLUSTER),  // PULP Cluster interface (incl. cv.elw)
        .FPU                (soc_config_pkg::CORE_CONF_FPU),  // Floating Point Unit (interfaced via APU interface)
        .FPU_ADDMUL_LAT     (soc_config_pkg::CORE_CONF_FPU_ADDMUL_LAT),  // Floating-Point ADDition/MULtiplication computing lane pipeline registers number
        .FPU_OTHERS_LAT     (soc_config_pkg::CORE_CONF_FPU_OTHERS_LAT),  // Floating-Point COMParison/CONVersion computing lanes pipeline registers number
        .ZFINX              (soc_config_pkg::CORE_CONF_ZFINX),  // Float-in-General Purpose registers
        .NUM_MHPMCOUNTERS   (soc_config_pkg::CORE_CONF_NUM_MHPMCOUNTERS)
    ) CORE_CV32E40P (
        // Clock and Reset
        .clk_i                  (clk_i      ),
        .rst_ni                 (~reset_i   ),
        
        // PULP clock enable (only used if COREV_CLUSTER = 1)
        .pulp_clock_en_i        ( 1'b0),
        // Enable all clock gates for testing
        .scan_cg_en_i           ( 1'b1),  
        
        // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
        .boot_addr_i            ( CORE_boot_addr_w              ),
        .mtvec_addr_i           ( CORE_mtvec_addr_w             ),
        .dm_halt_addr_i         ( CORE_dm_halt_addr_w           ),
        .hart_id_i              ( CORE_hart_id_w                ),
        .dm_exception_addr_i    ( CORE_dm_exception_addr_w      ),
        
        // Instruction memory interface
        .instr_req_o            ( CORE_instr_intf.instr_req     ),
        .instr_gnt_i            ( CORE_instr_intf.instr_gnt     ),
        .instr_rvalid_i         ( CORE_instr_intf.instr_rvalid  ),
        .instr_addr_o           ( CORE_instr_intf.instr_addr    ),
        .instr_rdata_i          ( CORE_instr_intf.instr_rdata   ),
        
        // Data memory interface
        .data_req_o             ( core_data_intf_req_w          ),
        .data_gnt_i             ( core_data_intf_gnt_w          ),
        .data_rvalid_i          ( CORE_data_intf.data_rvalid    ),
        .data_we_o              ( core_data_intf_we_w           ),
        .data_be_o              ( core_data_intf_be_w           ),
        .data_addr_o            ( core_data_intf_addr_w         ),
        .data_wdata_o           ( core_data_intf_data_w         ),
        .data_rdata_i           ( CORE_data_intf.data_rdata     ),
        
        // Interrupt inputs
        // CLINT interrupts + CLINT extension interrupts
        .irq_i                  ( 'd0),
        .irq_ack_o              (),
        .irq_id_o               (),
        
        // Debug Interface
        .debug_req_i            ( 1'b0),
        .debug_havereset_o      (),
        .debug_running_o        (),
        .debug_halted_o         (),
        
        // CPU Control Signals
        .fetch_enable_i         (1'b1),
        .core_sleep_o           ()
    );
    
    core_instruction_top
    #(
        .ROM_SIZE_IN_BYTE       (1024),
        .INST_MEM_SIZE_IN_KB    (8),
            
        /// AXI4-Lite address width.
        .AxiAddrWidth           (soc_config_pkg::AXI4_CONF_ADDR_WIDTH),
        /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
        .AxiDataWidth           (soc_config_pkg::AXI4_CONF_DATA_WIDTH),
        /// AXI4+ATOP ID width.
        .AxiID_WIDTH            (soc_config_pkg::AXI4_CONF_ID_WIDTH),
        /// AXI4+ATOP user width.
        .AxiUSER_WIDTH          (soc_config_pkg::AXI4_CONF_USER_WIDTH)
    ) CORE_INSTR_CONTROLLER (
        .clk_i(clk_i), .reset_i(reset_i),
        
        // Core Intsruction Interface
        .CORE_inst_inf_i(CORE_instr_intf),
        
        .slv(AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID])
    );
    
    core_data_top
    #(
        .DATA_MEM_SIZE_IN_KB    (8),
        
        /// AXI4-Lite address width.
        .AxiAddrWidth           (soc_config_pkg::AXI4_CONF_ADDR_WIDTH),
        /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
        .AxiDataWidth           (soc_config_pkg::AXI4_CONF_DATA_WIDTH),
        /// AXI4+ATOP ID width.
        .AxiID_WIDTH            (soc_config_pkg::AXI4_CONF_ID_WIDTH),
        /// AXI4+ATOP user width.
        .AxiUSER_WIDTH          (soc_config_pkg::AXI4_CONF_USER_WIDTH)
    ) CORE_DATA_CONTROLLER (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .CORE_data_inf_i        ( CORE_data_intf                        ),
        
        .axi_master             ( AXI4_Masters[AXI4_MASTER_CORE_ID]     ),
        .axi_slv                ( AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID]  )
    );
    
    /*
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_id = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_addr = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_len = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_size = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_burst = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_lock = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_cache = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_prot = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_qos = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_region = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_atop = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_user = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].aw_valid = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].w_data = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].w_strb = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].w_last = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].w_user = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].w_valid = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].b_ready = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_id = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_addr = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_len = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_size = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_burst = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_lock = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_cache = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_prot = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_qos = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_region = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_user = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].ar_valid = '0;
    assign AXI4_Masters[AXI4_MASTER_CORE_ID].r_ready = '0;

    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].aw_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].w_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].b_id = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].b_resp = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].b_user = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].b_valid = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].ar_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_id = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_data = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_resp = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_last = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_user = '0;
    assign AXI4_Slaves[AXI4_SLAVE_DATA_SRAM_ID].r_valid = '0;
    
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].aw_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].w_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].b_id = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].b_resp = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].b_user = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].b_valid = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].ar_ready = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_id = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_data = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_resp = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_last = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_user = '0;
    assign AXI4_Slaves[AXI4_SLAVE_INST_SRAM_ID].r_valid = '0;
    */
    
    /*
    soc_peripherals_top
    #(
        .AXI_ADDR_WIDTH     (soc_config_pkg::AXI4_CONF_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (soc_config_pkg::AXI4_CONF_DATA_WIDTH),
        .AXI_ID_WIDTH       (soc_config_pkg::AXI4_CONF_ID_WIDTH),
        .AXI_USER_WIDTH     (soc_config_pkg::AXI4_CONF_USER_WIDTH)
    ) SOC_PERIPHERALS_CONTROLLER (
        .clk_i(clk_i), .reset_i(reset_i),
        
        .PERIPHERAL_INTF(PERIPHERAL_INTF),
        
        .AXI4_slave(AXI4_Slaves[AXI4_SLAVE_PERIPHERALS_ID])
    );
    */
    
    /// Configuration for `axi_xbar`.
    localparam axi_pkg::xbar_cfg_t SOC_SystemBus_xbar_cfg = '{
        /// Number of slave ports of the crossbar.
        /// This many master modules are connected to it.
        // int unsigned   NoSlvPorts;
        NoSlvPorts:         SYSTEM_BUS_MASTER_COUNT,
        /// Number of master ports of the crossbar.
        /// This many slave modules are connected to it.
        // int unsigned   NoMstPorts;
        NoMstPorts:         SYSTEM_BUS_SLAVE_COUNT,
        /// Maximum number of open transactions each master connected to the crossbar can have in
        /// flight at the same time.
        // int unsigned   MaxMstTrans;
        MaxMstTrans:        SYSTEM_BUS_SLAVE_COUNT,
        /// Maximum number of open transactions each slave connected to the crossbar can have in
        /// flight at the same time.
        // int unsigned   MaxSlvTrans;
        MaxSlvTrans:        SYSTEM_BUS_MASTER_COUNT,
        /// Determine if the internal FIFOs of the crossbar are instantiated in fallthrough mode.
        /// 0: No fallthrough
        /// 1: Fallthrough
        // bit            FallThrough;
        FallThrough:        1'b0,
        /// The Latency mode of the xbar. This determines if the channels on the ports have
        /// a spill register instantiated.
        /// Example configurations are provided with the enum `xbar_latency_e`.
        // bit [9:0]      LatencyMode;
        LatencyMode:        axi_pkg::CUT_ALL_AX,
        /// This is the number of `axi_multicut` stages instantiated in the line cross of the channels.
        /// Having multiple stages can potentially add a large number of FFs!
        // int unsigned   PipelineStages;
        PipelineStages:     32'd2,
        /// AXI ID width of the salve ports. The ID width of the master ports is determined
        /// Automatically. See `axi_mux` for details.
        // int unsigned   AxiIdWidthSlvPorts;
        AxiIdWidthSlvPorts: soc_config_pkg::AXI4_CONF_ID_WIDTH,
        /// The used ID portion to determine if a different salve is used for the same ID.
        /// See `axi_demux` for details.
        // int unsigned   AxiIdUsedSlvPorts;
        AxiIdUsedSlvPorts:  32'd3,
        /// Are IDs unique?
        // bit            UniqueIds;
        UniqueIds:          32'd0,
        /// AXI4+ATOP address field width.
        // int unsigned   AxiAddrWidth;
        AxiAddrWidth:       soc_config_pkg::AXI4_CONF_ADDR_WIDTH,
        /// AXI4+ATOP data field width.
        // int unsigned   AxiDataWidth;
        AxiDataWidth:       soc_config_pkg::AXI4_CONF_DATA_WIDTH,
        /// The number of address rules defined for routing of the transactions.
        /// Each master port can have multiple rules, should have however at least one.
        /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
        // int unsigned   NoAddrRules;
        NoAddrRules:        SYSTEM_BUS_SLAVE_COUNT
    };
    
    axi_xbar_intf
    #(
        .AXI_USER_WIDTH     (soc_config_pkg::AXI4_CONF_USER_WIDTH   ),
        .Cfg                (SOC_SystemBus_xbar_cfg                 ),
        .rule_t             (axi_pkg::xbar_rule_32_t                )
    ) SYSTEM_BUS (
        .clk_i                  (clk_i),
        .rst_ni                 (~reset_i),
        .test_i                 (1'b0),
        
        .slv_ports              (AXI4_Masters),
        .mst_ports              (AXI4_Slaves),
        
        .addr_map_i             (AXI4_AddrMap),
        
        .en_default_mst_port_i  ('0),
        .default_mst_port_i     ('0)
    );
    
endmodule




















