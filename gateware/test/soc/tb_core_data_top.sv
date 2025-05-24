`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 19.05.2025 08:36:57
// Design Name: 
// Module Name: tb_core_data_top
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


module tb_core_data_top();

    localparam T=10;
    logic clk, reset;
    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        reset=1'b1;
        #(T*5);
        reset='b0;
    end
    
    localparam time CyclTime = 10ns;
    localparam time ApplTime =  2ns;
    localparam time TestTime =  8ns;
    
    localparam DATA_MEM_SIZE_IN_KB = 8;

    localparam int unsigned AXI_ADDR_WIDTH = 32;
    localparam int unsigned AXI_DATA_WIDTH = 32;
    localparam int unsigned AXI_ID_WIDTH   = 8;
    localparam int unsigned AXI_USER_WIDTH = 8;
    
    CORE_DATA_INF CORE_data_inf_i();
    
    AXI_BUS #(
        .AXI_ADDR_WIDTH (  AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH (  AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   (  AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH (  AXI_USER_WIDTH )
    ) AXI4_master();
    
    AXI_BUS #(
        .AXI_ADDR_WIDTH (  AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH (  AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   (  AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH (  AXI_USER_WIDTH )
    ) AXI4_slave();

    typedef logic [AXI_ID_WIDTH-1:0]        id_mst_t;
    typedef logic [AXI_ID_WIDTH-1:0]        id_slv_t;
    typedef logic [AXI_ADDR_WIDTH-1:0]      addr_t;
    typedef axi_pkg::xbar_rule_32_t         rule_t; // Has to be the same width as axi addr
    typedef logic [AXI_DATA_WIDTH-1:0]      data_t;
    typedef logic [(AXI_DATA_WIDTH/8)-1:0]  strb_t;
    typedef logic [AXI_USER_WIDTH-1:0]      user_t;
    
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, user_t)
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_mst_t, id_mst_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)
    
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_mst_t, data_t, id_mst_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)
    
    `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t)
    `AXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_mst_t, r_chan_mst_t)
    `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
    `AXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_slv_t, r_chan_slv_t)

    slv_req_t   slaves_req;
    slv_resp_t  slaves_resp;

    core_data_top
    #(
        .DATA_MEM_SIZE_IN_KB(DATA_MEM_SIZE_IN_KB),
            
        /// AXI4-Lite address width.
        .AxiAddrWidth           ( AXI_ADDR_WIDTH    ),
        /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
        .AxiDataWidth           ( AXI_DATA_WIDTH    ),
        /// AXI4+ATOP ID width.
        .AxiID_WIDTH            ( AXI_ID_WIDTH      ),
        /// AXI4+ATOP user width.
        .AxiUSER_WIDTH          ( AXI_USER_WIDTH    )
    )
    DUT
    (
        .clk_i(clk), .reset_i(reset),
        
        .CORE_data_inf_i(CORE_data_inf_i),
        
        .axi_master(AXI4_master),
        .axi_slv(AXI4_slave)
    );
    
    `AXI_ASSIGN_TO_REQ(slaves_req, AXI4_slave)
    `AXI_ASSIGN_TO_RESP(slaves_resp, AXI4_slave)
    
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_masterPort")),
      .aw_chan_t ( aw_chan_slv_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_slv_t ), // axi  B type
      .ar_chan_t ( ar_chan_slv_t ), // axi AR type
      .r_chan_t  (  r_chan_slv_t )  // axi  R type
    ) i_slv_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( ~reset      ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( 1'b0        ),
      // AW channel
      .aw_chan_i  ( slaves_req.aw        ),
      .aw_valid_i ( slaves_req.aw_valid  ),
      .aw_ready_i ( slaves_resp.aw_ready ),
      //  W channel
      .w_chan_i   ( slaves_req.w         ),
      .w_valid_i  ( slaves_req.w_valid   ),
      .w_ready_i  ( slaves_resp.w_ready  ),
      //  B channel
      .b_chan_i   ( slaves_resp.b        ),
      .b_valid_i  ( slaves_resp.b_valid  ),
      .b_ready_i  ( slaves_req.b_ready   ),
      // AR channel
      .ar_chan_i  ( slaves_req.ar        ),
      .ar_valid_i ( slaves_req.ar_valid  ),
      .ar_ready_i ( slaves_resp.ar_ready ),
      //  R channel
      .r_chan_i   ( slaves_resp.r        ),
      .r_valid_i  ( slaves_resp.r_valid  ),
      .r_ready_i  ( slaves_req.r_ready   )
    );
    
    initial begin
        AXI4_slave.aw_id = 1'b0;
        AXI4_slave.aw_addr = 'b0;
        AXI4_slave.aw_len = 'b0;
        AXI4_slave.aw_size = 'b0;
        AXI4_slave.aw_burst = 'b0;
        AXI4_slave.aw_lock = 'b0;
        AXI4_slave.aw_cache = 'b0;
        AXI4_slave.aw_prot = 'b0;
        AXI4_slave.aw_qos = 'b0;
        AXI4_slave.aw_region = 'b0;
        AXI4_slave.aw_atop = 'b0;
        AXI4_slave.aw_user = 'b0;
        AXI4_slave.aw_valid = 'b0;
        
        AXI4_slave.w_data = 'b0;
        AXI4_slave.w_strb = 'b0;
        AXI4_slave.w_last = 'b0;
        AXI4_slave.w_user = 'b0;
        AXI4_slave.w_valid = 'b0;
        
        AXI4_slave.b_ready = 'b0;
        
        AXI4_slave.ar_id = 'b0;
        AXI4_slave.ar_addr = 'b0;
        AXI4_slave.ar_len = 'b0;
        AXI4_slave.ar_size = 'b0;
        AXI4_slave.ar_burst = 'b0;
        AXI4_slave.ar_lock = 'b0;
        AXI4_slave.ar_cache = 'b0;
        AXI4_slave.ar_prot = 'b0;
        AXI4_slave.ar_qos = 'b0;
        AXI4_slave.ar_user = 'b0;
        AXI4_slave.ar_valid = 'b0;
        
        AXI4_slave.r_ready = 1'b0;
        
        
        CORE_data_inf_i.data_addr = 'b0;
        CORE_data_inf_i.data_req = 'b0;
        CORE_data_inf_i.data_we = 'b0;
        CORE_data_inf_i.data_be = 'b0;
        CORE_data_inf_i.data_wdata = 'b0;
        CORE_data_inf_i.data_gnt = 'b0;
        CORE_data_inf_i.data_rvalid = 'b0;
        CORE_data_inf_i.data_rdata = 'b0;
    end
    
    task AXI4_WRITE;
        input [AXI_ADDR_WIDTH-1:0] addr; 
        input [AXI_DATA_WIDTH-1:0] data;
    
        begin
            // Address Write Channel
            @(posedge clk);
            AXI4_slave.aw_valid <= 1;
            AXI4_slave.aw_addr  <= addr;
            AXI4_slave.aw_id    <= 0;
            AXI4_slave.aw_len   <= 0; // single beat
            AXI4_slave.aw_size  <= $clog2(AXI_DATA_WIDTH/8); // word access
            AXI4_slave.aw_burst <= 2'b01; // INCR
            AXI4_slave.aw_lock  <= 0;
            AXI4_slave.aw_cache <= 0;
            AXI4_slave.aw_prot  <= 0;
            AXI4_slave.aw_qos   <= 0;
            AXI4_slave.aw_user  <= 0;
    
            // Wait for aw_ready
            wait (AXI4_slave.aw_ready);
            @(posedge clk);
            AXI4_slave.aw_valid <= 0;
    
            // Write Data Channel
            AXI4_slave.w_valid <= 1;
            AXI4_slave.w_data  <= data;
            AXI4_slave.w_strb  <= {AXI_DATA_WIDTH/8{1'b1}}; // write all bytes
            AXI4_slave.w_last  <= 1;
            AXI4_slave.w_user  <= 0;
    
            // Wait for w_ready
            wait (AXI4_slave.w_ready);
            @(posedge clk);
            AXI4_slave.w_valid <= 0;
    
            // Write Response Channel
            AXI4_slave.b_ready <= 1;
            wait (AXI4_slave.b_valid);
            @(posedge clk);
            AXI4_slave.b_ready <= 0;
        end
    endtask

    
    task AXI4_READ;
        input  [AXI_ADDR_WIDTH-1:0] addr; 
        output [AXI_DATA_WIDTH-1:0] data;
    
        begin
            // Address Read Channel
            @(posedge clk);
            AXI4_slave.ar_valid <= 1;
            AXI4_slave.ar_addr  <= addr;
            AXI4_slave.ar_id    <= 0;
            AXI4_slave.ar_len   <= 0;
            AXI4_slave.ar_size  <= $clog2(AXI_DATA_WIDTH/8); 
            AXI4_slave.ar_burst <= 2'b01;
            AXI4_slave.ar_lock  <= 0;
            AXI4_slave.ar_cache <= 0;
            AXI4_slave.ar_prot  <= 0;
            AXI4_slave.ar_qos   <= 0;
            AXI4_slave.ar_user  <= 0;
    
            // Wait for ar_ready
            wait (AXI4_slave.ar_ready);
            @(posedge clk);
            AXI4_slave.ar_valid <= 0;
    
            // Read Data Channel
            AXI4_slave.r_ready <= 1;
            wait (AXI4_slave.r_valid);
            data = AXI4_slave.r_data;
            @(posedge clk);
            AXI4_slave.r_ready <= 0;
        end
    endtask
    
    task DATA_READ;
        input  logic [31:0] addr;
        output logic [31:0] data;
    
        begin
            @(posedge clk);
            CORE_data_inf_i.data_addr <= addr;
            CORE_data_inf_i.data_req  <= 1'b1;
            CORE_data_inf_i.data_we   <= 1'b0;  // Read
            CORE_data_inf_i.data_be   <= 4'b1111;
    
            // Grant bekleniyor
            wait (CORE_data_inf_i.data_gnt == 1'b1);
            @(posedge clk);
            CORE_data_inf_i.data_req <= 1'b0;
    
            // Response (rvalid) bekleniyor
            wait (CORE_data_inf_i.data_rvalid == 1'b1);
            data = CORE_data_inf_i.data_rdata;
    
            @(posedge clk);
        end
    endtask
    
    task DATA_WRITE;
        input  logic [31:0] addr;
        input  logic [31:0] data;
    
        begin
            @(posedge clk);
            CORE_data_inf_i.data_addr  <= addr;
            CORE_data_inf_i.data_req   <= 1'b1;
            CORE_data_inf_i.data_we    <= 1'b1;  // Write
            CORE_data_inf_i.data_be    <= 4'b1111;
            CORE_data_inf_i.data_wdata <= data;
    
            // Grant bekleniyor
            wait (CORE_data_inf_i.data_gnt == 1'b1);
            @(posedge clk);
            CORE_data_inf_i.data_req <= 1'b0;
    
            // Yazma işleminde rvalid kontrolü opsiyoneldir, istenirse eklenebilir
            @(posedge clk);
        end
    endtask
    
    initial begin
        repeat(5) @(posedge clk);
        
        AXI4_WRITE(32'h3000_0000, 32'hbeafbeef);
        
        repeat(5) @(posedge clk);
        $finish;
    end

endmodule




































