`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 11:13:05
// Design Name: 
// Module Name: tb_axi2mem
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

module tb_axi2mem();

    `SIM_CLK_RST(10, 5, 100)

    localparam integer CORE_ADDR_WIDTH                 = 32;
    localparam integer CORE_DATA_WIDTH                 = 32;
    localparam integer CORE_BE_WIDTH                   = 4;
    localparam integer ID_WIDTH                        = 8;
    localparam integer ADDR_WIDTH                      = 32;
    localparam integer USER_WIDTH                      = 8;
    localparam integer S_DATA_WIDTH                    = 32;
    localparam integer S_STRB_WIDTH                    = 4;
    
    logic [CORE_ADDR_WIDTH-1:0] core_data_addr_o;
    logic                       core_data_req_o;
    logic                       core_data_we_o;
    logic [CORE_BE_WIDTH-1:0]   core_data_be_o;
    logic [CORE_DATA_WIDTH-1:0] core_data_wdata_o;
    logic                       core_data_gnt_i;
    logic                       core_data_rvalid_i;
    logic [CORE_DATA_WIDTH-1:0] core_data_rdata_i;
    
    /*
    * AXI slave interface
    */
    logic [ID_WIDTH-1:0]        s_axi_awid;
    logic [ADDR_WIDTH-1:0]      s_axi_awaddr;
    logic [7:0]                 s_axi_awlen;
    logic [2:0]                 s_axi_awsize;
    logic [1:0]                 s_axi_awburst;
    logic                       s_axi_awlock;
    logic [3:0]                 s_axi_awcache;
    logic [2:0]                 s_axi_awprot;
    logic [3:0]                 s_axi_awqos;
    logic [3:0]                 s_axi_awregion;
    logic [USER_WIDTH-1:0]      s_axi_awuser;
    logic                       s_axi_awvalid;
    logic                       s_axi_awready;
    logic [S_DATA_WIDTH-1:0]    s_axi_wdata;
    logic [S_STRB_WIDTH-1:0]    s_axi_wstrb;
    logic                       s_axi_wlast;
    logic [USER_WIDTH-1:0]      s_axi_wuser;
    logic                       s_axi_wvalid;
    logic                       s_axi_wready;
    logic [ID_WIDTH-1:0]        s_axi_bid;
    logic [1:0]                 s_axi_bresp;
    logic [USER_WIDTH-1:0]      s_axi_buser;
    logic                       s_axi_bvalid;
    logic                       s_axi_bready;
    logic [ID_WIDTH-1:0]        s_axi_arid;
    logic [ADDR_WIDTH-1:0]      s_axi_araddr;
    logic [7:0]                 s_axi_arlen;
    logic [2:0]                 s_axi_arsize;
    logic [1:0]                 s_axi_arburst;
    logic                       s_axi_arlock;
    logic [3:0]                 s_axi_arcache;
    logic [2:0]                 s_axi_arprot;
    logic [3:0]                 s_axi_arqos;
    logic [3:0]                 s_axi_arregion;
    logic [USER_WIDTH-1:0]      s_axi_aruser;
    logic                       s_axi_arvalid;
    logic                       s_axi_arready;
    logic [ID_WIDTH-1:0]        s_axi_rid;
    logic [S_DATA_WIDTH-1:0]    s_axi_rdata;
    logic [1:0]                 s_axi_rresp;
    logic                       s_axi_rlast;
    logic [USER_WIDTH-1:0]      s_axi_ruser;
    logic                       s_axi_rvalid;
    logic                       s_axi_rready;

    axi2mem #(
        .CORE_ADDR_WIDTH        ( CORE_ADDR_WIDTH      ),
        .CORE_DATA_WIDTH        ( CORE_DATA_WIDTH      ),
        .CORE_BE_WIDTH          ( CORE_BE_WIDTH        ),
        .ID_WIDTH               ( ID_WIDTH             ),
        .ADDR_WIDTH             ( ADDR_WIDTH           ),
        .USER_WIDTH             ( USER_WIDTH           ),
        .S_DATA_WIDTH           ( S_DATA_WIDTH         ),
        .S_STRB_WIDTH           ( S_STRB_WIDTH         )
    ) DUT (
        .clk_i(`CLK), 
        .reset_ni(`RST),
        
        .core_data_addr_o       ( core_data_addr_o      ),
        .core_data_req_o        ( core_data_req_o       ),
        .core_data_we_o         ( core_data_we_o        ),
        .core_data_be_o         ( core_data_be_o        ),
        .core_data_wdata_o      ( core_data_wdata_o     ),
        .core_data_gnt_i        ( core_data_gnt_i       ),
        .core_data_rvalid_i     ( core_data_rvalid_i    ),
        .core_data_rdata_i      ( core_data_rdata_i     ),
        
        /*
        * AXI slave interface
        */
        .s_axi_awid             ( s_axi_awid            ),
        .s_axi_awaddr           ( s_axi_awaddr          ),
        .s_axi_awlen            ( s_axi_awlen           ),
        .s_axi_awsize           ( s_axi_awsize          ),
        .s_axi_awburst          ( s_axi_awburst         ),
        .s_axi_awlock           ( s_axi_awlock          ),
        .s_axi_awcache          ( s_axi_awcache         ),
        .s_axi_awprot           ( s_axi_awprot          ),
        .s_axi_awqos            ( s_axi_awqos           ),
        .s_axi_awregion         ( s_axi_awregion        ),
        .s_axi_awuser           ( s_axi_awuser          ),
        .s_axi_awvalid          ( s_axi_awvalid         ),
        .s_axi_awready          ( s_axi_awready         ),
        .s_axi_wdata            ( s_axi_wdata           ),
        .s_axi_wstrb            ( s_axi_wstrb           ),
        .s_axi_wlast            ( s_axi_wlast           ),
        .s_axi_wuser            ( s_axi_wuser           ),
        .s_axi_wvalid           ( s_axi_wvalid          ),
        .s_axi_wready           ( s_axi_wready          ),
        .s_axi_bid              ( s_axi_bid             ),
        .s_axi_bresp            ( s_axi_bresp           ),
        .s_axi_buser            ( s_axi_buser           ),
        .s_axi_bvalid           ( s_axi_bvalid          ),
        .s_axi_bready           ( s_axi_bready          ),
        .s_axi_arid             ( s_axi_arid            ),
        .s_axi_araddr           ( s_axi_araddr          ),
        .s_axi_arlen            ( s_axi_arlen           ),
        .s_axi_arsize           ( s_axi_arsize          ),
        .s_axi_arburst          ( s_axi_arburst         ),
        .s_axi_arlock           ( s_axi_arlock          ),
        .s_axi_arcache          ( s_axi_arcache         ),
        .s_axi_arprot           ( s_axi_arprot          ),
        .s_axi_arqos            ( s_axi_arqos           ),
        .s_axi_arregion         ( s_axi_arregion        ),
        .s_axi_aruser           ( s_axi_aruser          ),
        .s_axi_arvalid          ( s_axi_arvalid         ),
        .s_axi_arready          ( s_axi_arready         ),
        .s_axi_rid              ( s_axi_rid             ),
        .s_axi_rdata            ( s_axi_rdata           ),
        .s_axi_rresp            ( s_axi_rresp           ),
        .s_axi_rlast            ( s_axi_rlast           ),
        .s_axi_ruser            ( s_axi_ruser           ),
        .s_axi_rvalid           ( s_axi_rvalid          ),
        .s_axi_rready           ( s_axi_rready          )
    );
    
    class Rand_axi_req;
        randc logic [ID_WIDTH-1:0]        s_axi_awid;
        randc logic [ADDR_WIDTH-1:0]      s_axi_awaddr;
        randc logic [S_DATA_WIDTH-1:0]    s_axi_wdata;
    endclass
    
    Rand_axi_req RAxi;
    
    task PIN_RESET;
        AW_CHANNEL_DONE;
        W_CHANNEL_DONE;
        B_CHANNEL_DONE;
        AR_CHANNEL_DONE;
        R_CHANNEL_DONE;
        
        RAxi=new();
    endtask

    task AW_CHANNEL_START;
        input integer id, addr;
        
        begin
            s_axi_awid      = id;
            s_axi_awaddr    = addr;
            
            s_axi_awlen     = 0;
            s_axi_awsize    = 0;
            s_axi_awburst   = 0;
            s_axi_awlock    = 0;
            s_axi_awcache   = 0;
            s_axi_awprot    = 0;
            s_axi_awqos     = 0;
            s_axi_awregion  = 0;
            s_axi_awuser    = 0;
           
            s_axi_awvalid   = 1'b1;
        end
    endtask
    
    task AW_CHANNEL_DONE;
        begin
            s_axi_awid      = 'dx;
            s_axi_awaddr    = 'dx;
            
            s_axi_awlen     = 0;
            s_axi_awsize    = 0;
            s_axi_awburst   = 0;
            s_axi_awlock    = 0;
            s_axi_awcache   = 0;
            s_axi_awprot    = 0;
            s_axi_awqos     = 0;
            s_axi_awregion  = 0;
            s_axi_awuser    = 0;
           
            s_axi_awvalid   = 1'b0;
        end
    endtask
    
    task W_CHANNEL_START;
        input integer data;
        
        begin
            s_axi_wdata     = data;
            s_axi_wstrb     = -1;
            s_axi_wlast     = 1;
            s_axi_wuser     = 0;
            s_axi_wvalid    = 1'b1;
        end
    endtask
    
    task W_CHANNEL_DONE;
        begin
            s_axi_wdata     = 'dx;
            s_axi_wstrb     = 0;
            s_axi_wlast     = 0;
            s_axi_wuser     = 0;
            s_axi_wvalid    = 1'b0;
        end
    endtask
    
    task B_CHANNEL_START;
        begin
            s_axi_bready  = 1'b1;
        end
    endtask
    
    task B_CHANNEL_DONE;
        begin
            s_axi_bready  = 1'b0;
        end
    endtask
    
    task AR_CHANNEL_START;
        input integer id, addr;
        
        begin
            s_axi_arid     = id;
            s_axi_araddr   = addr;
            s_axi_arlen    = 0;
            s_axi_arsize   = 0;
            s_axi_arburst  = 0;
            s_axi_arlock   = 0;
            s_axi_arcache  = 0;
            s_axi_arprot   = 0;
            s_axi_arqos    = 0;
            s_axi_arregion = 0;
            s_axi_aruser   = 0;
            s_axi_arvalid  = 1'b1;
        end
    endtask
    
    task AR_CHANNEL_DONE;
        begin
            s_axi_arid     = 'dx;
            s_axi_araddr   = 'dx;
            s_axi_arlen    = 0;
            s_axi_arsize   = 0;
            s_axi_arburst  = 0;
            s_axi_arlock   = 0;
            s_axi_arcache  = 0;
            s_axi_arprot   = 0;
            s_axi_arqos    = 0;
            s_axi_arregion = 0;
            s_axi_aruser   = 0;
            s_axi_arvalid  = 1'b0;
        end
    endtask
    
    task R_CHANNEL_START;
        begin
            s_axi_rready = 1'b1;
        end
    endtask
    
    task R_CHANNEL_DONE;
        begin
            s_axi_rready = 1'b0;
        end
    endtask
    
    initial begin
        PIN_RESET;
        
        `WAIT_SIM
        
        `CYCLE
        `CYCLE
        
        begin : TEST001
            RAxi.randomize();
            AW_CHANNEL_START(RAxi.s_axi_awid, RAxi.s_axi_awaddr);
            W_CHANNEL_START(RAxi.s_axi_wdata);
            `CYCLE
            AW_CHANNEL_DONE;
            W_CHANNEL_DONE;
            core_data_gnt_i = 1'b1;
            core_data_rvalid_i = 1'b1;
            #(1ps);
            `COMPARE((core_data_req_o === 1'b1),
                $sformatf("TEST001: req error, must be high"))
            `COMPARE((core_data_we_o === 1'b1),
                $sformatf("TEST001: write enable error, must be high"))
            `COMPARE((core_data_addr_o === RAxi.s_axi_awaddr),
                $sformatf("TEST001: addr error, read: %8h, test: %8h",
                    core_data_addr_o,
                    RAxi.s_axi_awaddr
                ))
            `COMPARE((core_data_wdata_o === RAxi.s_axi_wdata),
                $sformatf("TEST001: data error, read: %8h, test: %8h",
                    core_data_wdata_o,
                    RAxi.s_axi_wdata
                ))
            `COMPARE((core_data_be_o === -4'd1),
                $sformatf("TEST001: data error, read: %4b, test: %4b",
                    core_data_be_o,
                    -4'd1
                ))
            `CYCLE
            core_data_gnt_i = 1'b0;
            core_data_rvalid_i = 1'b0;
            B_CHANNEL_START;
            `CYCLE
            B_CHANNEL_DONE;
        end
        
        begin : TEST002
            RAxi.randomize();
            AR_CHANNEL_START(RAxi.s_axi_awid, RAxi.s_axi_awaddr);
            R_CHANNEL_START;
            `CYCLE
            AR_CHANNEL_DONE;
            core_data_gnt_i = 1'b1;
            s_axi_rdata = RAxi.s_axi_wdata;
            core_data_rvalid_i = 1'b1;
            #(1ps);
            `COMPARE((core_data_req_o === 1'b1),
                $sformatf("TEST002: req error, must be high"))
            `COMPARE((core_data_we_o === 1'b0),
                $sformatf("TEST002: write enable error, must be high"))
            `COMPARE((core_data_addr_o === RAxi.s_axi_awaddr),
                $sformatf("TEST002: addr error, read: %8h, test: %8h",
                    core_data_addr_o,
                    RAxi.s_axi_awaddr
                ))
            `COMPARE((s_axi_rdata === RAxi.s_axi_wdata),
                $sformatf("TEST002: data error, read: %8h, test: %8h",
                    s_axi_rdata,
                    RAxi.s_axi_wdata
                ))
            `CYCLE
            core_data_gnt_i = 1'b0;
            core_data_rvalid_i = 1'b0;
            `CYCLE
            R_CHANNEL_DONE;
        end
        
        `CYCLEN(5)
        `SIM_STOP
    end
    
endmodule


















