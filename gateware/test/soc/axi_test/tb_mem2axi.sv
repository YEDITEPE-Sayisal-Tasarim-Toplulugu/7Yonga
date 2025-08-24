`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 13:07:14
// Design Name: 
// Module Name: tb_mem2axi
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

`include "tb_common.svh"

module tb_mem2axi();
    
    `SIM_CLK_RST(10, 5, 100)
    
    localparam integer CORE_ADDR_WIDTH      = 32;
    localparam integer CORE_DATA_WIDTH      = 32;
    localparam integer CORE_BE_WIDTH        = 4;
    localparam integer ID_WIDTH             = 8;
    localparam integer ADDR_WIDTH           = 32;
    localparam integer USER_WIDTH           = 8;
    localparam integer M_DATA_WIDTH         = 32;
    localparam integer M_STRB_WIDTH         = 4;
    
    logic [CORE_ADDR_WIDTH-1:0] core_data_addr_i;
    logic                       core_data_req_i;
    logic                       core_data_we_i;
    logic [CORE_BE_WIDTH-1:0]   core_data_be_i;
    logic [CORE_DATA_WIDTH-1:0] core_data_wdata_i;
    logic                       core_data_gnt_o;
    logic                       core_data_rvalid_o;
    logic [CORE_DATA_WIDTH-1:0] core_data_rdata_o;
    
    logic [ID_WIDTH-1:0]        m_axi_awid;
    logic [ADDR_WIDTH-1:0]      m_axi_awaddr;
    logic [7:0]                 m_axi_awlen;
    logic [2:0]                 m_axi_awsize;
    logic [1:0]                 m_axi_awburst;
    logic                       m_axi_awlock;
    logic [3:0]                 m_axi_awcache;
    logic [2:0]                 m_axi_awprot;
    logic [3:0]                 m_axi_awqos;
    logic [3:0]                 m_axi_awregion;
    logic [USER_WIDTH-1:0]      m_axi_awuser;
    logic                       m_axi_awvalid;
    logic                       m_axi_awready;
    logic [M_DATA_WIDTH-1:0]    m_axi_wdata;
    logic [M_STRB_WIDTH-1:0]    m_axi_wstrb;
    logic                       m_axi_wlast;
    logic [USER_WIDTH-1:0]      m_axi_wuser;
    logic                       m_axi_wvalid;
    logic                       m_axi_wready;
    logic [ID_WIDTH-1:0]        m_axi_bid;
    logic [1:0]                 m_axi_bresp;
    logic [USER_WIDTH-1:0]      m_axi_buser;
    logic                       m_axi_bvalid;
    logic                       m_axi_bready;
    logic [ID_WIDTH-1:0]        m_axi_arid;
    logic [ADDR_WIDTH-1:0]      m_axi_araddr;
    logic [7:0]                 m_axi_arlen;
    logic [2:0]                 m_axi_arsize;
    logic [1:0]                 m_axi_arburst;
    logic                       m_axi_arlock;
    logic [3:0]                 m_axi_arcache;
    logic [2:0]                 m_axi_arprot;
    logic [3:0]                 m_axi_arqos;
    logic [3:0]                 m_axi_arregion;
    logic [USER_WIDTH-1:0]      m_axi_aruser;
    logic                       m_axi_arvalid;
    logic                       m_axi_arready;
    logic [ID_WIDTH-1:0]        m_axi_rid;
    logic [M_DATA_WIDTH-1:0]    m_axi_rdata;
    logic [1:0]                 m_axi_rresp;
    logic                       m_axi_rlast;
    logic [USER_WIDTH-1:0]      m_axi_ruser;
    logic                       m_axi_rvalid;
    logic                       m_axi_rready;
    
    mem2axi #(
        .CORE_ADDR_WIDTH     ( CORE_ADDR_WIDTH      ),
        .CORE_DATA_WIDTH     ( CORE_DATA_WIDTH      ),
        .CORE_BE_WIDTH       ( CORE_BE_WIDTH        ),
        .ID_WIDTH            ( ID_WIDTH             ),
        .ADDR_WIDTH          ( ADDR_WIDTH           ),
        .USER_WIDTH          ( USER_WIDTH           ),
        .M_DATA_WIDTH        ( M_DATA_WIDTH         ),
        .M_STRB_WIDTH        ( M_STRB_WIDTH         )
    ) DUT (
        .clk_i(`CLK), 
        .reset_ni(`RST),
        
        .core_data_addr_i   ( core_data_addr_i      ),
        .core_data_req_i    ( core_data_req_i       ),
        .core_data_we_i     ( core_data_we_i        ),
        .core_data_be_i     ( core_data_be_i        ),
        .core_data_wdata_i  ( core_data_wdata_i     ),
        .core_data_gnt_o    ( core_data_gnt_o       ),
        .core_data_rvalid_o ( core_data_rvalid_o    ),
        .core_data_rdata_o  ( core_data_rdata_o     ),
        
        .m_axi_awid         ( m_axi_awid            ),
        .m_axi_awaddr       ( m_axi_awaddr          ),
        .m_axi_awlen        ( m_axi_awlen           ),
        .m_axi_awsize       ( m_axi_awsize          ),
        .m_axi_awburst      ( m_axi_awburst         ),
        .m_axi_awlock       ( m_axi_awlock          ),
        .m_axi_awcache      ( m_axi_awcache         ),
        .m_axi_awprot       ( m_axi_awprot          ),
        .m_axi_awqos        ( m_axi_awqos           ),
        .m_axi_awregion     ( m_axi_awregion        ),
        .m_axi_awuser       ( m_axi_awuser          ),
        .m_axi_awvalid      ( m_axi_awvalid         ),
        .m_axi_awready      ( m_axi_awready         ),
        .m_axi_wdata        ( m_axi_wdata           ),
        .m_axi_wstrb        ( m_axi_wstrb           ),
        .m_axi_wlast        ( m_axi_wlast           ),
        .m_axi_wuser        ( m_axi_wuser           ),
        .m_axi_wvalid       ( m_axi_wvalid          ),
        .m_axi_wready       ( m_axi_wready          ),
        .m_axi_bid          ( m_axi_bid             ),
        .m_axi_bresp        ( m_axi_bresp           ),
        .m_axi_buser        ( m_axi_buser           ),
        .m_axi_bvalid       ( m_axi_bvalid          ),
        .m_axi_bready       ( m_axi_bready          ),
        .m_axi_arid         ( m_axi_arid            ),
        .m_axi_araddr       ( m_axi_araddr          ),
        .m_axi_arlen        ( m_axi_arlen           ),
        .m_axi_arsize       ( m_axi_arsize          ),
        .m_axi_arburst      ( m_axi_arburst         ),
        .m_axi_arlock       ( m_axi_arlock          ),
        .m_axi_arcache      ( m_axi_arcache         ),
        .m_axi_arprot       ( m_axi_arprot          ),
        .m_axi_arqos        ( m_axi_arqos           ),
        .m_axi_arregion     ( m_axi_arregion        ),
        .m_axi_aruser       ( m_axi_aruser          ),
        .m_axi_arvalid      ( m_axi_arvalid         ),
        .m_axi_arready      ( m_axi_arready         ),
        .m_axi_rid          ( m_axi_rid             ),
        .m_axi_rdata        ( m_axi_rdata           ),
        .m_axi_rresp        ( m_axi_rresp           ),
        .m_axi_rlast        ( m_axi_rlast           ),
        .m_axi_ruser        ( m_axi_ruser           ),
        .m_axi_rvalid       ( m_axi_rvalid          ),
        .m_axi_rready       ( m_axi_rready          )
    );
    
    class Rand_axi_req;
        randc logic [ADDR_WIDTH-1:0]      addr;
        randc logic [M_DATA_WIDTH-1:0]    data;
    endclass
    
    Rand_axi_req RAxi;
    
    task PIN_RESET;
        CORE_WRITE_DONE;
        CORE_READ_DONE;
    
        m_axi_awready = 1'b0;
        m_axi_wready = 1'b0;
        m_axi_bvalid = 1'b0;
        m_axi_arready = 1'b0;
        m_axi_rready = 1'b0;
    
        RAxi=new();
    endtask
    
    task CORE_WRITE_START;
        input integer addr;
        input integer data;
        
        begin
            core_data_addr_i    = addr;
            core_data_req_i     = 1'b1;
            core_data_we_i      = 1'b1;
            core_data_be_i      = -4'd1;
            core_data_wdata_i   = data;
        end
    endtask
    
    task CORE_WRITE_DONE;
        begin
            core_data_addr_i    = 'dx;
            core_data_req_i     = 1'b0;
            core_data_we_i      = 1'b0;
            core_data_be_i      = 4'd0;
            core_data_wdata_i   = 'dx;
        end
    endtask
    
    task CORE_READ_START;
        input integer addr;
        
        begin
            core_data_addr_i    = addr;
            core_data_req_i     = 1'b1;
            core_data_we_i      = 1'b0;
            core_data_be_i      = -4'd1;
            core_data_wdata_i   = 'dx;
        end
    endtask
    
    task CORE_READ_DONE;
        begin
            core_data_addr_i    = 'dx;
            core_data_req_i     = 1'b0;
            core_data_we_i      = 1'b0;
            core_data_be_i      = 4'd0;
            core_data_wdata_i   = 'dx;
        end
    endtask
    
    initial begin
        PIN_RESET;
        
        `WAIT_SIM
        
        `CYCLE
        `CYCLE
        
        begin : TEST001
            RAxi.randomize();
            CORE_WRITE_START(RAxi.addr, RAxi.data);
            `CYCLE
            CORE_WRITE_DONE;
            m_axi_awready = 1'b1;
            m_axi_wready = 1'b1;
            m_axi_bvalid = 1'b1;
            #(1ps);
            `COMPARE((m_axi_awvalid === 1'b1),
                $sformatf("TEST001: aw valid, must be high"))
            `COMPARE((m_axi_awaddr === RAxi.addr),
                $sformatf("TEST001: addr error, read: %8h, test: %8h",
                    m_axi_awaddr,
                    RAxi.addr
                ))
            `COMPARE((m_axi_wvalid === 1'b1),
                $sformatf("TEST001: w valid, must be high"))
            `COMPARE((m_axi_wdata === RAxi.data),
                $sformatf("TEST001: data error, read: %8h, test: %8h",
                    m_axi_wdata,
                    RAxi.data
                ))
            `COMPARE((m_axi_wstrb === -4'd1),
                $sformatf("TEST001: be error, read: %8h, test: %8h",
                    m_axi_wstrb,
                    -4'd1
                ))
            `COMPARE((m_axi_bready === 1'b1),
                $sformatf("TEST001: m_axi_bready, must be high"))
            `CYCLE
            m_axi_awready = 1'b0;
            m_axi_wready = 1'b0;
            m_axi_bvalid = 1'b0;
            #(1ps);
            `COMPARE((core_data_gnt_o === 1'b1),
                $sformatf("TEST001: core_data_gnt_o, must be high"))
            `COMPARE((core_data_rvalid_o === 1'b1),
                $sformatf("TEST001: core_data_rvalid_o, must be high"))
        end
        
        `CYCLEN(5)
        `SIM_STOP
    end
    
endmodule















