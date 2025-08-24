`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 09:39:00
// Design Name: 
// Module Name: mem2axi
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


module mem2axi
    #(parameter
            CORE_ADDR_WIDTH                 = 32,
            CORE_DATA_WIDTH                 = 32,
            CORE_BE_WIDTH                   = 4,
            ID_WIDTH                        = 8,
            ADDR_WIDTH                      = 32,
            USER_WIDTH                      = 8,
            M_DATA_WIDTH                    = 32,
            M_STRB_WIDTH                    = 4
    )
    (
        input   logic                       clk_i, reset_ni,
        
        input   logic [CORE_ADDR_WIDTH-1:0] core_data_addr_i,
        input   logic                       core_data_req_i,
        input   logic                       core_data_we_i,
        input   logic [CORE_BE_WIDTH-1:0]   core_data_be_i,
        input   logic [CORE_DATA_WIDTH-1:0] core_data_wdata_i,
        output  logic                       core_data_gnt_o,
        output  logic                       core_data_rvalid_o,
        output  logic [CORE_DATA_WIDTH-1:0] core_data_rdata_o,
        
        output  logic [ID_WIDTH-1:0]        m_axi_awid,
        output  logic [ADDR_WIDTH-1:0]      m_axi_awaddr,
        output  logic [7:0]                 m_axi_awlen,
        output  logic [2:0]                 m_axi_awsize,
        output  logic [1:0]                 m_axi_awburst,
        output  logic                       m_axi_awlock,
        output  logic [3:0]                 m_axi_awcache,
        output  logic [2:0]                 m_axi_awprot,
        output  logic [3:0]                 m_axi_awqos,
        output  logic [3:0]                 m_axi_awregion,
        output  logic [USER_WIDTH-1:0]      m_axi_awuser,
        output  logic                       m_axi_awvalid,
        input   logic                       m_axi_awready,
        output  logic [M_DATA_WIDTH-1:0]    m_axi_wdata,
        output  logic [M_STRB_WIDTH-1:0]    m_axi_wstrb,
        output  logic                       m_axi_wlast,
        output  logic [USER_WIDTH-1:0]      m_axi_wuser,
        output  logic                       m_axi_wvalid,
        input   logic                       m_axi_wready,
        input   logic [ID_WIDTH-1:0]        m_axi_bid,
        input   logic [1:0]                 m_axi_bresp,
        input   logic [USER_WIDTH-1:0]      m_axi_buser,
        input   logic                       m_axi_bvalid,
        output  logic                       m_axi_bready,
        output  logic [ID_WIDTH-1:0]        m_axi_arid,
        output  logic [ADDR_WIDTH-1:0]      m_axi_araddr,
        output  logic [7:0]                 m_axi_arlen,
        output  logic [2:0]                 m_axi_arsize,
        output  logic [1:0]                 m_axi_arburst,
        output  logic                       m_axi_arlock,
        output  logic [3:0]                 m_axi_arcache,
        output  logic [2:0]                 m_axi_arprot,
        output  logic [3:0]                 m_axi_arqos,
        output  logic [3:0]                 m_axi_arregion,
        output  logic [USER_WIDTH-1:0]      m_axi_aruser,
        output  logic                       m_axi_arvalid,
        input   logic                       m_axi_arready,
        input   logic [ID_WIDTH-1:0]        m_axi_rid,
        input   logic [M_DATA_WIDTH-1:0]    m_axi_rdata,
        input   logic [1:0]                 m_axi_rresp,
        input   logic                       m_axi_rlast,
        input   logic [USER_WIDTH-1:0]      m_axi_ruser,
        input   logic                       m_axi_rvalid,
        output  logic                       m_axi_rready
    );
    
    logic                       core_data_req_r;
    logic [CORE_ADDR_WIDTH-1:0] core_data_addr_r;
    logic                       core_data_we_r;
    logic [CORE_BE_WIDTH-1:0]   core_data_be_r;
    logic [CORE_DATA_WIDTH-1:0] core_data_data_r;
    
    logic                       axi_aw_ready_r;
    logic                       axi_w_ready_r;
    logic                       axi_b_ready_r;
    
    logic                       axi_ar_ready_r;
    logic                       axi_r_ready_r;
    
    assign m_axi_awid           = 0;
    assign m_axi_awaddr         = core_data_addr_r;
    assign m_axi_awlen          = 0;
    assign m_axi_awsize         = 0;
    assign m_axi_awburst        = 0;
    assign m_axi_awlock         = 0;
    assign m_axi_awcache        = 0;
    assign m_axi_awprot         = 0;
    assign m_axi_awqos          = 0;
    assign m_axi_awregion       = 0;
    assign m_axi_awuser         = 0;
    assign m_axi_awvalid        = core_data_req_r & core_data_we_r & ~axi_aw_ready_r;
    
    assign m_axi_wdata          = core_data_data_r;
    assign m_axi_wstrb          = core_data_be_r;
    assign m_axi_wlast          = 1;
    assign m_axi_wuser          = 0;
    assign m_axi_wvalid         = core_data_req_r & core_data_we_r & ~axi_w_ready_r;
    
    assign m_axi_bready         = core_data_req_r & (axi_aw_ready_r & axi_w_ready_r & axi_b_ready_r);
    
    assign m_axi_arid           = 0;
    assign m_axi_araddr         = core_data_addr_r;
    assign m_axi_arlen          = 0;
    assign m_axi_arsize         = 0;
    assign m_axi_arburst        = 0;
    assign m_axi_arlock         = 0;
    assign m_axi_arcache        = 0;
    assign m_axi_arprot         = 0;
    assign m_axi_arqos          = 0;
    assign m_axi_arregion       = 0;
    assign m_axi_aruser         = 0;
    assign m_axi_arvalid        = core_data_req_r & ~core_data_we_r & ~axi_ar_ready_r;
    
    assign m_axi_rready         = core_data_req_r & (axi_ar_ready_r & axi_r_ready_r);
    
    assign core_data_gnt_o      = core_data_req_r & ((core_data_we_r) 
        ? (axi_aw_ready_r & axi_w_ready_r & axi_b_ready_r) : (axi_ar_ready_r & axi_r_ready_r));
    assign core_data_rvalid_o   = core_data_req_r & ((core_data_we_r) 
        ? (axi_aw_ready_r & axi_w_ready_r & axi_b_ready_r) : (axi_ar_ready_r & axi_r_ready_r));
    assign core_data_rdata_o    = m_axi_rdata;
    
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            core_data_req_r     <= 0;
            core_data_addr_r    <= 0;
            core_data_we_r      <= 0;
            core_data_be_r      <= 0;
            core_data_data_r    <= 0;
            
            axi_aw_ready_r      <= 0;
            axi_w_ready_r       <= 0;
            axi_b_ready_r       <= 0;
            
            axi_ar_ready_r      <= 0;
            axi_r_ready_r       <= 0;
        end else begin
            if (~core_data_req_r & core_data_req_i) begin
                core_data_req_r     <= 1'b1;
                core_data_addr_r    <= core_data_addr_i;
                core_data_we_r      <= core_data_we_i;
                core_data_be_r      <= core_data_be_i;
                core_data_data_r    <= core_data_wdata_i;
                
                axi_aw_ready_r      <= 0;
                axi_w_ready_r       <= 0;
                axi_b_ready_r       <= 0;
                
                axi_ar_ready_r      <= 0;
                axi_r_ready_r       <= 0;
            end else begin
                axi_aw_ready_r      <= axi_aw_ready_r | m_axi_awready;
                axi_w_ready_r       <= axi_w_ready_r | m_axi_wready;
                axi_b_ready_r       <= axi_b_ready_r | m_axi_bvalid;
                
                axi_ar_ready_r      <= axi_ar_ready_r | m_axi_arready;
                axi_r_ready_r       <= axi_r_ready_r | m_axi_rvalid;
                
                if (
                    (axi_aw_ready_r & axi_w_ready_r & axi_b_ready_r) |
                    (axi_ar_ready_r & axi_r_ready_r)
                ) begin
                    core_data_req_r <= 1'b0;
                end
            end
        end
    end
    
endmodule




















