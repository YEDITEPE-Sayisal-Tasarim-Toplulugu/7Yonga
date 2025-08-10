`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 09:39:00
// Design Name: 
// Module Name: axi2mem
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


module axi2mem
    #(parameter
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
        
        output  logic [CORE_ADDR_WIDTH-1:0] core_data_addr_o,
        output  logic                       core_data_req_o,
        output  logic                       core_data_we_o,
        output  logic [CORE_BE_WIDTH-1:0]   core_data_be_o,
        output  logic [CORE_DATA_WIDTH-1:0] core_data_wdata_o,
        input   logic                       core_data_gnt_i,
        input   logic                       core_data_rvalid_i,
        input   logic [CORE_DATA_WIDTH-1:0] core_data_rdata_i,
        
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
    
    logic                       s_axi_addr_valid_r;
    logic                       s_axi_w_valid_r;
    logic                       s_axi_r_valid_r;
    logic                       s_axi_slave_valid_r;
    
    logic [ADDR_WIDTH-1:0]      s_axi_addr_r;
    logic [ID_WIDTH-1:0]        s_axi_id_r;
    logic [S_DATA_WIDTH-1:0]    s_axi_data_r;
    logic [S_STRB_WIDTH-1:0]    s_axi_wstrb_r;
    
    logic                       mem_gnt_r;
    
    // AW Channel
    assign s_axi_awready        = ~s_axi_addr_valid_r;
    
    // W Channel
    assign s_axi_wready         = ~s_axi_w_valid_r;
    
    // B Channel
    assign s_axi_bid            = s_axi_id_r;
    assign s_axi_bresp          = 2'b00;
    assign s_axi_buser          = 0;
    assign s_axi_bvalid         = s_axi_addr_valid_r & s_axi_slave_valid_r & s_axi_w_valid_r;
    
    // AR Channel
    assign s_axi_arready        = ~s_axi_addr_valid_r;
    
    // R Channel
    assign s_axi_rid            = s_axi_id_r;
    assign s_axi_rdata          = s_axi_data_r;
    assign s_axi_rresp          = 2'b00;
    assign s_axi_rlast          = 1'b1;
    assign s_axi_ruser          = 0;
    assign s_axi_rvalid         = s_axi_addr_valid_r & s_axi_slave_valid_r & s_axi_r_valid_r;
    
    assign core_data_addr_o     = s_axi_addr_r;
    assign core_data_req_o      = (s_axi_addr_valid_r & (s_axi_w_valid_r | s_axi_r_valid_r)) & ~mem_gnt_r;
    assign core_data_we_o       = s_axi_w_valid_r;
    assign core_data_be_o       = s_axi_wstrb_r;
    assign core_data_wdata_o    = s_axi_data_r;
    
    localparam integer IDLE=0, WDATA=1, WRITE=2, READ=3;
    logic [7:0] status_r;
    
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            status_r            <= IDLE;
            
            s_axi_addr_valid_r  <= 0;
            s_axi_w_valid_r     <= 0;
            s_axi_r_valid_r     <= 0;
            s_axi_slave_valid_r <= 0;
                                
            s_axi_addr_r        <= 0;
            s_axi_id_r          <= 0;
            s_axi_data_r        <= 0;
            s_axi_wstrb_r       <= 0;

            mem_gnt_r           <= 0;
        end else begin
            if (s_axi_wvalid & ~s_axi_w_valid_r) begin
                s_axi_data_r <= s_axi_wdata;
                s_axi_wstrb_r <= s_axi_wstrb;
                s_axi_w_valid_r <= 1'b1; 
            end else if (s_axi_addr_valid_r & s_axi_w_valid_r & s_axi_bready & s_axi_slave_valid_r) begin
                s_axi_w_valid_r <= 1'b0;
            end
        
            case (status_r)
                IDLE: begin
                    s_axi_addr_valid_r  <= 0;
                    s_axi_r_valid_r     <= 0;
                    s_axi_slave_valid_r <= 0;
                    mem_gnt_r           <= 0;
                    
                    if (s_axi_awvalid) begin
                        s_axi_id_r <= s_axi_awid;
                        s_axi_addr_r <= s_axi_awaddr;
                        
                        s_axi_addr_valid_r <= 1'b1;
                        s_axi_r_valid_r <= 1'b0;
                        
                        status_r <= WRITE;
                    end else if (s_axi_arvalid) begin
                        s_axi_id_r <= s_axi_arid;
                        s_axi_addr_r <= s_axi_araddr;
                        
                        s_axi_addr_valid_r <= 1'b1;
                        s_axi_r_valid_r <= 1'b1;
                        
                        status_r <= READ;
                    end
                end
                
                WRITE: begin
                    if (s_axi_w_valid_r) begin
                        mem_gnt_r <= core_data_gnt_i;
                    end
                    
                    if (core_data_rvalid_i) begin
                        s_axi_slave_valid_r <= 1'b1;
                    end
                    
                    if (s_axi_slave_valid_r & s_axi_bready) begin
                        status_r <= IDLE;
                    end
                end
                
                READ: begin
                    s_axi_data_r <= core_data_rdata_i;
                    
                    s_axi_slave_valid_r <= 1'b1;
                    
                    mem_gnt_r <= core_data_gnt_i;
                    
                    if (s_axi_rready) begin
                        status_r <= IDLE;
                    end
                end
                
                default: begin
                    s_axi_addr_valid_r  <= 0;
                    s_axi_r_valid_r     <= 0;
                    s_axi_slave_valid_r <= 0;
                    mem_gnt_r           <= 0;
                    
                    status_r            <= IDLE;
                end
            endcase
        end
    end
    
endmodule


















