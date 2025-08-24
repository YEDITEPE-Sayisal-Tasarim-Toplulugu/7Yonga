`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.08.2025 21:09:15
// Design Name: 
// Module Name: core_inst_top_v2
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

`include "sverilog_utils.svh"
`include "soc_configuration.svh"
`include "soc_addr_rules.svh"

module core_inst_top_v2
    import soc_addr_rules_pkg::*;
    #(parameter
            INST_MEMORY_SIZE_IN_KB          = 8,
            CORE_ADDR_WIDTH                 = 32,
            CORE_DATA_WIDTH                 = 32,
            CORE_BE_WIDTH                   = 4,
            ID_WIDTH                        = 8,
            ADDR_WIDTH                      = 32,
            USER_WIDTH                      = 8,
            S_DATA_WIDTH                    = 32,
            S_STRB_WIDTH                    = 4
    )
    (
        input   logic                       clk_i, reset_ni,
        
        input   logic                       programmer_mem_write_enable_i,
        input   logic [31:0]                programmer_mem_write_addr_i,
        input   logic [31:0]                programmer_mem_write_data_i,
        
        input   logic [CORE_ADDR_WIDTH-1:0] core_instr_addr_i,
        input   logic                       core_instr_req_i,
        output  logic                       core_instr_gnt_o,
        output  logic                       core_instr_rvalid_o,
        output  logic [31:0]                core_instr_rdata_o,
        
        /*
        * AXI slave interface
        */
        input   logic [ID_WIDTH-1:0]        s_axi_awid,
        input   logic [ADDR_WIDTH-1:0]      s_axi_awaddr,
        input   logic [7:0]                 s_axi_awlen,
        input   logic [2:0]                 s_axi_awsize,
        input   logic [1:0]                 s_axi_awburst,
        input   logic                       s_axi_awlock,
        input   logic [3:0]                 s_axi_awcache,
        input   logic [2:0]                 s_axi_awprot,
        input   logic [3:0]                 s_axi_awqos,
        input   logic [3:0]                 s_axi_awregion,
        input   logic [USER_WIDTH-1:0]      s_axi_awuser,
        input   logic                       s_axi_awvalid,
        output  logic                       s_axi_awready,
        input   logic [S_DATA_WIDTH-1:0]    s_axi_wdata,
        input   logic [S_STRB_WIDTH-1:0]    s_axi_wstrb,
        input   logic                       s_axi_wlast,
        input   logic [USER_WIDTH-1:0]      s_axi_wuser,
        input   logic                       s_axi_wvalid,
        output  logic                       s_axi_wready,
        output  logic [ID_WIDTH-1:0]        s_axi_bid,
        output  logic [1:0]                 s_axi_bresp,
        output  logic [USER_WIDTH-1:0]      s_axi_buser,
        output  logic                       s_axi_bvalid,
        input   logic                       s_axi_bready,
        input   logic [ID_WIDTH-1:0]        s_axi_arid,
        input   logic [ADDR_WIDTH-1:0]      s_axi_araddr,
        input   logic [7:0]                 s_axi_arlen,
        input   logic [2:0]                 s_axi_arsize,
        input   logic [1:0]                 s_axi_arburst,
        input   logic                       s_axi_arlock,
        input   logic [3:0]                 s_axi_arcache,
        input   logic [2:0]                 s_axi_arprot,
        input   logic [3:0]                 s_axi_arqos,
        input   logic [3:0]                 s_axi_arregion,
        input   logic [USER_WIDTH-1:0]      s_axi_aruser,
        input   logic                       s_axi_arvalid,
        output  logic                       s_axi_arready,
        output  logic [ID_WIDTH-1:0]        s_axi_rid,
        output  logic [S_DATA_WIDTH-1:0]    s_axi_rdata,
        output  logic [1:0]                 s_axi_rresp,
        output  logic                       s_axi_rlast,
        output  logic [USER_WIDTH-1:0]      s_axi_ruser,
        output  logic                       s_axi_rvalid,
        input   logic                       s_axi_rready
    );
    
    logic decoder_sel_w, decoder_illegal_w, arbiter_sel_w;
    logic [1:0] arbiter_ready_list_w;
    
    logic arbiter_stage1_sel_w, decoder_stage2_sel_w;
    
    logic [CORE_ADDR_WIDTH-1:0] CVT_data_addr_w;
    logic                       CVT_data_req_w;
    logic                       CVT_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   CVT_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] CVT_data_wdata_w;
    logic                       CVT_data_gnt_w;
    logic                       CVT_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] CVT_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] axi_slave_data_addr_w;
    logic                       axi_slave_data_req_w;
    logic                       axi_slave_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   axi_slave_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] axi_slave_data_wdata_w;
    logic                       axi_slave_data_gnt_w;
    logic                       axi_slave_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] axi_slave_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] ARBITER_data_addr_w;
    logic                       ARBITER_data_req_w;
    logic                       ARBITER_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   ARBITER_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] ARBITER_data_wdata_w;
    logic                       ARBITER_data_gnt_w;
    logic                       ARBITER_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] ARBITER_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] DECODER1_data_addr_w;
    logic                       DECODER1_data_req_w;
    logic                       DECODER1_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   DECODER1_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] DECODER1_data_wdata_w;
    logic                       DECODER1_data_gnt_w;
    logic                       DECODER1_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] DECODER1_data_rdata_w;
    
    logic [CORE_ADDR_WIDTH-1:0] DECODER2_data_addr_w;
    logic                       DECODER2_data_req_w;
    logic                       DECODER2_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   DECODER2_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] DECODER2_data_wdata_w;
    logic                       DECODER2_data_gnt_w;
    logic                       DECODER2_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] DECODER2_data_rdata_w;
    
    typedef logic decoder_id_t;
    
    typedef struct packed {
        decoder_id_t    id;
        addr_t          start_addr;
        addr_t          end_addr;
    } intf_decoder_addr_rule_t;
    
    intf_decoder_addr_rule_t decoder_addr_rule_w [0:1];
    assign decoder_addr_rule_w[0].id            = 0;
    assign decoder_addr_rule_w[0].start_addr    = soc_addr_rules_pkg::ROM_ADDR_RULE.start_addr;
    assign decoder_addr_rule_w[0].end_addr      = soc_addr_rules_pkg::ROM_ADDR_RULE.end_addr;
    assign decoder_addr_rule_w[1].id            = 1;
    assign decoder_addr_rule_w[1].start_addr    = soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.start_addr;
    assign decoder_addr_rule_w[1].end_addr      = soc_addr_rules_pkg::INST_SRAM_ADDR_RULE.end_addr;
    
    // Arbiter
    assign arbiter_ready_list_w[0]      = CVT_data_req_w;
    assign arbiter_ready_list_w[1]      = axi_slave_data_req_w;
    
    assign ARBITER_data_addr_w          = (arbiter_stage1_sel_w) ? axi_slave_data_addr_w  : CVT_data_addr_w  ;
    assign ARBITER_data_req_w           = (arbiter_stage1_sel_w) ? axi_slave_data_req_w   : CVT_data_req_w   ;
    assign ARBITER_data_we_w            = (arbiter_stage1_sel_w) ? axi_slave_data_we_w    : CVT_data_we_w    ;
    assign ARBITER_data_be_w            = (arbiter_stage1_sel_w) ? axi_slave_data_be_w    : CVT_data_be_w    ;
    assign ARBITER_data_wdata_w         = (arbiter_stage1_sel_w) ? axi_slave_data_wdata_w : CVT_data_wdata_w ;
    
    assign CVT_data_gnt_w               = (arbiter_stage1_sel_w) ? 0 : ARBITER_data_gnt_w ;
    assign CVT_data_rvalid_w            = (arbiter_stage1_sel_w) ? 0 : ARBITER_data_rvalid_w ;
    assign CVT_data_rdata_w             = ARBITER_data_rdata_w;
    
    assign axi_slave_data_gnt_w         = (arbiter_stage1_sel_w) ? ARBITER_data_gnt_w    :  0;
    assign axi_slave_data_rvalid_w      = (arbiter_stage1_sel_w) ? ARBITER_data_rvalid_w :  0;
    assign axi_slave_data_rdata_w       = ARBITER_data_rdata_w;
    
    // Decoder
    assign ARBITER_data_gnt_w           = (decoder_stage2_sel_w) ? DECODER2_data_gnt_w    : DECODER1_data_gnt_w    ;
    assign ARBITER_data_rvalid_w        = (decoder_stage2_sel_w) ? DECODER2_data_rvalid_w : DECODER1_data_rvalid_w ;
    assign ARBITER_data_rdata_w         = (decoder_stage2_sel_w) ? DECODER2_data_rdata_w  : DECODER1_data_rdata_w  ;
    
    assign DECODER1_data_addr_w         = ARBITER_data_addr_w; 
    assign DECODER1_data_req_w          = (decoder_stage2_sel_w) ? 0 : ARBITER_data_req_w;  
    assign DECODER1_data_we_w           = ARBITER_data_we_w;   
    assign DECODER1_data_be_w           = ARBITER_data_be_w;   
    assign DECODER1_data_wdata_w        = ARBITER_data_wdata_w;
    
    assign DECODER2_data_addr_w         = ARBITER_data_addr_w;
    assign DECODER2_data_req_w          = (decoder_stage2_sel_w) ? ARBITER_data_req_w : 0;
    assign DECODER2_data_we_w           = ARBITER_data_we_w;
    assign DECODER2_data_be_w           = ARBITER_data_be_w;
    assign DECODER2_data_wdata_w        = ARBITER_data_wdata_w;
    
    logic arbiter_stege1_valid_r, decoder_stage2_valid_r;
    logic arbiter_stage1_sel_r, decoder_stege2_sel_r;
    assign arbiter_stage1_sel_w = (arbiter_stege1_valid_r) ? arbiter_stage1_sel_r : arbiter_sel_w;
    assign decoder_stage2_sel_w = (decoder_stage2_valid_r) ? decoder_stege2_sel_r : decoder_sel_w;
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            arbiter_stege1_valid_r <= 0;
            decoder_stage2_valid_r <= 0;
            arbiter_stage1_sel_r <= 0;
            decoder_stege2_sel_r <= 0;
        end else begin
            if (arbiter_stege1_valid_r) begin
                if (ARBITER_data_rvalid_w) begin
                    arbiter_stege1_valid_r <= 1'b0;
                end
            end else if (ARBITER_data_req_w) begin
                arbiter_stege1_valid_r <= 1'b1;
                arbiter_stage1_sel_r <= arbiter_sel_w;
            end
            
            if (decoder_stage2_valid_r) begin
                if (ARBITER_data_rvalid_w) begin
                    decoder_stage2_valid_r <= 1'b0;
                end
            end else if (ARBITER_data_req_w) begin
                decoder_stage2_valid_r <= 1'b1;
                decoder_stege2_sel_r <= decoder_sel_w;
            end
        end 
    end
    
    cv32e_inst2data_inf_cvt #(
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH           ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH           ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH             )
    ) INST2DATA (
        .instr_addr_i           ( core_instr_addr_i         ),
        .instr_req_i            ( core_instr_req_i          ),
        .instr_gnt_o            ( core_instr_gnt_o          ),
        .instr_rvalid_o         ( core_instr_rvalid_o       ),
        .instr_rdata_o          ( core_instr_rdata_o        ),
        
        .data_addr_o            ( CVT_data_addr_w           ),
        .data_req_o             ( CVT_data_req_w            ),
        .data_we_o              ( CVT_data_we_w             ),
        .data_be_o              ( CVT_data_be_w             ),
        .data_wdata_o           ( CVT_data_wdata_w          ),
        .data_gnt_i             ( CVT_data_gnt_w            ),
        .data_rvalid_i          ( CVT_data_rvalid_w         ),
        .data_rdata_i           ( CVT_data_rdata_w          )
    );
    
    roundrobin_arbiter #(
        .PORT_COUNT             ( 2                         ),
        .PRIORTY_AT_0           ( 1                         ),
        
        .PORT_ID_WIDTH          ( 1                         )
    ) INTERFACE_ARBITER (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .port_ready_list_i      ( arbiter_ready_list_w      ),
        .port_selected_id_o     ( arbiter_sel_w             )
    ); 
    
    addr_decode #(
        .ID_TYPE                ( decoder_id_t              ),
        .ADDR_TYPE              ( soc_addr_rules_pkg::addr_t),
        .RULE_TYPE              ( intf_decoder_addr_rule_t  ),
        
        .PORT_COUNT             ( 2                         )
    ) INTERFACE_DECODER (
        .addr_rule_map_i        ( decoder_addr_rule_w       ),
        .addr_i                 ( ARBITER_data_addr_w       ),
        .illegal_o              ( decoder_illegal_w         ),
        .selected_id_o          ( decoder_sel_w             )
    );
    
    axi2mem #(
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH           ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH           ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH             ),
        .ID_WIDTH               ( ID_WIDTH                  ),
        .ADDR_WIDTH             ( ADDR_WIDTH                ),
        .USER_WIDTH             ( USER_WIDTH                ),
        .S_DATA_WIDTH           ( S_DATA_WIDTH              ),
        .S_STRB_WIDTH           ( S_STRB_WIDTH              )
    ) AXI2MEM (
        .clk_i(clk_i), .reset_ni(reset_ni),
        
        .core_data_addr_o       ( axi_slave_data_addr_w     ),
        .core_data_req_o        ( axi_slave_data_req_w      ),
        .core_data_we_o         ( axi_slave_data_we_w       ),
        .core_data_be_o         ( axi_slave_data_be_w       ),
        .core_data_wdata_o      ( axi_slave_data_wdata_w    ),
        .core_data_gnt_i        ( axi_slave_data_gnt_w      ),
        .core_data_rvalid_i     ( axi_slave_data_rvalid_w   ),
        .core_data_rdata_i      ( axi_slave_data_rdata_w    ),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( s_axi_awid                ),
        .s_axi_awaddr           ( s_axi_awaddr              ),
        .s_axi_awlen            ( s_axi_awlen               ),
        .s_axi_awsize           ( s_axi_awsize              ),
        .s_axi_awburst          ( s_axi_awburst             ),
        .s_axi_awlock           ( s_axi_awlock              ),
        .s_axi_awcache          ( s_axi_awcache             ),
        .s_axi_awprot           ( s_axi_awprot              ),
        .s_axi_awqos            ( s_axi_awqos               ),
        .s_axi_awregion         ( s_axi_awregion            ),
        .s_axi_awuser           ( s_axi_awuser              ),
        .s_axi_awvalid          ( s_axi_awvalid             ),
        .s_axi_awready          ( s_axi_awready             ),
        .s_axi_wdata            ( s_axi_wdata               ),
        .s_axi_wstrb            ( s_axi_wstrb               ),
        .s_axi_wlast            ( s_axi_wlast               ),
        .s_axi_wuser            ( s_axi_wuser               ),
        .s_axi_wvalid           ( s_axi_wvalid              ),
        .s_axi_wready           ( s_axi_wready              ),
        .s_axi_bid              ( s_axi_bid                 ),
        .s_axi_bresp            ( s_axi_bresp               ),
        .s_axi_buser            ( s_axi_buser               ),
        .s_axi_bvalid           ( s_axi_bvalid              ),
        .s_axi_bready           ( s_axi_bready              ),
        .s_axi_arid             ( s_axi_arid                ),
        .s_axi_araddr           ( s_axi_araddr              ),
        .s_axi_arlen            ( s_axi_arlen               ),
        .s_axi_arsize           ( s_axi_arsize              ),
        .s_axi_arburst          ( s_axi_arburst             ),
        .s_axi_arlock           ( s_axi_arlock              ),
        .s_axi_arcache          ( s_axi_arcache             ),
        .s_axi_arprot           ( s_axi_arprot              ),
        .s_axi_arqos            ( s_axi_arqos               ),
        .s_axi_arregion         ( s_axi_arregion            ),
        .s_axi_aruser           ( s_axi_aruser              ),
        .s_axi_arvalid          ( s_axi_arvalid             ),
        .s_axi_arready          ( s_axi_arready             ),
        .s_axi_rid              ( s_axi_rid                 ),
        .s_axi_rdata            ( s_axi_rdata               ),
        .s_axi_rresp            ( s_axi_rresp               ),
        .s_axi_rlast            ( s_axi_rlast               ),
        .s_axi_ruser            ( s_axi_ruser               ),
        .s_axi_rvalid           ( s_axi_rvalid              ),
        .s_axi_rready           ( s_axi_rready              )
    );
    
    inst_rom ROM_MEMORY (
        .clk_i(clk_i), .reset_ni(reset_ni),
    
        .instr_addr_i           ( DECODER1_data_addr_w      ),
        .instr_req_i            ( DECODER1_data_req_w       ),
        .instr_gnt_o            ( DECODER1_data_gnt_w       ),
        .instr_rvalid_o         ( DECODER1_data_rvalid_w    ),
        .instr_rdata_o          ( DECODER1_data_rdata_w     )
    );
    
    logic [CORE_ADDR_WIDTH-1:0] INSTRUCTION_MEMORY_data_addr_w;
    logic                       INSTRUCTION_MEMORY_data_req_w;
    logic                       INSTRUCTION_MEMORY_data_we_w;
    logic [CORE_BE_WIDTH-1:0]   INSTRUCTION_MEMORY_data_be_w;
    logic [CORE_DATA_WIDTH-1:0] INSTRUCTION_MEMORY_data_wdata_w;
    logic                       INSTRUCTION_MEMORY_data_gnt_w;
    logic                       INSTRUCTION_MEMORY_data_rvalid_w;
    logic [CORE_DATA_WIDTH-1:0] INSTRUCTION_MEMORY_data_rdata_w;
    
    assign INSTRUCTION_MEMORY_data_addr_w   = (programmer_mem_write_enable_i) ? programmer_mem_write_addr_i : DECODER2_data_addr_w ;
    assign INSTRUCTION_MEMORY_data_req_w    = (programmer_mem_write_enable_i) ? 1'b1 : DECODER2_data_req_w  ;
    assign INSTRUCTION_MEMORY_data_we_w     = (programmer_mem_write_enable_i) ? 1'b1 : DECODER2_data_we_w   ;
    assign INSTRUCTION_MEMORY_data_be_w     = (programmer_mem_write_enable_i) ? {(CORE_BE_WIDTH){1'b1}}: DECODER2_data_be_w   ;
    assign INSTRUCTION_MEMORY_data_wdata_w  = (programmer_mem_write_enable_i) ? programmer_mem_write_data_i : DECODER2_data_wdata_w;
    
    assign DECODER2_data_gnt_w              = (programmer_mem_write_enable_i) ? 0 : INSTRUCTION_MEMORY_data_gnt_w;   
    assign DECODER2_data_rvalid_w           = (programmer_mem_write_enable_i) ? 0 : INSTRUCTION_MEMORY_data_rvalid_w;
    assign DECODER2_data_rdata_w            = (programmer_mem_write_enable_i) ? 0 : INSTRUCTION_MEMORY_data_rdata_w; 
    
    inst_memory #(
        .SIZE_IN_KB             ( INST_MEMORY_SIZE_IN_KB    ),
        .ADDR_WIDTH             ( CORE_ADDR_WIDTH           ),
        .DATA_WIDTH             ( CORE_DATA_WIDTH           ),
        .BE_WIDTH               ( CORE_BE_WIDTH             )
    ) INSTRUCTION_MEMORY (
        .clk_i(clk_i), .reset_ni(reset_ni),

        .data_addr_i            ( INSTRUCTION_MEMORY_data_addr_w    ),
        .data_req_i             ( INSTRUCTION_MEMORY_data_req_w     ),
        .data_we_i              ( INSTRUCTION_MEMORY_data_we_w      ),
        .data_be_i              ( INSTRUCTION_MEMORY_data_be_w      ),
        .data_wdata_i           ( INSTRUCTION_MEMORY_data_wdata_w   ),
        .data_gnt_o             ( INSTRUCTION_MEMORY_data_gnt_w     ),
        .data_rvalid_o          ( INSTRUCTION_MEMORY_data_rvalid_w  ),
        .data_rdata_o           ( INSTRUCTION_MEMORY_data_rdata_w   )
    );
    
`ifdef ASSERTIONS
/*
    /////////////////////////////////////////
    // ASSERTIONS
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
        end else begin
            if (core_instr_req_i) begin
                `ASSERT((~decoder_illegal_w), 
                    $sformatf("core_data_top.sv: illegal decoded addr, addr data: %h", core_instr_addr_i))
            end
        end
    end
    /////////////////////////////////////////
*/
`endif // ASSERTIONS
    
endmodule




















