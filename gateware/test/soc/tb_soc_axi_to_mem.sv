`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 19.05.2025 09:00:28
// Design Name: 
// Module Name: tb_soc_axi_to_mem
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


module tb_soc_axi_to_mem();

    localparam T=10;
    logic clk, reset;
    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        reset=1'b1;
        #(T*5);
        reset='b0;
    end

    localparam int unsigned DATA_MEM_SIZE_IN_KB = 8;
    
    localparam int unsigned AXI_ADDR_WIDTH = 32;
    localparam int unsigned AXI_DATA_WIDTH = 32;
    localparam int unsigned AXI_ID_WIDTH   = 8;
    localparam int unsigned AXI_USER_WIDTH = 8;
    
    AXI_BUS #(
        .AXI_ADDR_WIDTH (  AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH (  AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   (  AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH (  AXI_USER_WIDTH )
    ) AXI4_slave();

    CORE_DATA_INF AXI4_ADAP_inf_w();
    /*
    axi_to_mem_intf #(
      /// See `axi_to_mem`, parameter `AddrWidth`.
      .ADDR_WIDTH     ( AXI_ADDR_WIDTH),
      /// See `axi_to_mem`, parameter `DataWidth`.
      .DATA_WIDTH     ( AXI_DATA_WIDTH),
      /// AXI4+ATOP ID width.
      .ID_WIDTH       ( AXI_ID_WIDTH),
      /// AXI4+ATOP user width.
      .USER_WIDTH     ( AXI_USER_WIDTH),
      /// See `axi_to_mem`, parameter `NumBanks`.
      .NUM_BANKS      ( 32'd1),
      /// See `axi_to_mem`, parameter `BufDepth`.
      .BUF_DEPTH      ( 32'd1),
      /// Hide write requests if the strb == '0
      .HIDE_STRB      ( 1'b0),
      /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
      .OUT_FIFO_DEPTH ( 32'd1)
    )
    DUT
    (
      /// Clock input.
      .clk_i(clk_i),
      /// Asynchronous reset, active low.
      .rst_ni(~reset_i),
      /// See `axi_to_mem`, port `busy_o`.
      .busy_o(),
      /// AXI4+ATOP slave interface port.
      .slv(AXI4_slave),
      /// See `axi_to_mem`, port `mem_req_o`.
      .mem_req_o(AXI4_ADAP_inf_w.data_req),
      /// See `axi_to_mem`, port `mem_gnt_i`.
      .mem_gnt_i(AXI4_ADAP_inf_w.data_gnt),
      /// See `axi_to_mem`, port `mem_addr_o`.
      .mem_addr_o(AXI4_ADAP_inf_w.data_addr),
      /// See `axi_to_mem`, port `mem_wdata_o`.
      .mem_wdata_o(AXI4_ADAP_inf_w.data_wdata),
      /// See `axi_to_mem`, port `mem_strb_o`.
      .mem_strb_o(AXI4_ADAP_inf_w.data_be),
      /// See `axi_to_mem`, port `mem_atop_o`.
      .mem_atop_o(),
      /// See `axi_to_mem`, port `mem_we_o`.
      .mem_we_o(AXI4_ADAP_inf_w.data_we),
      /// See `axi_to_mem`, port `mem_rvalid_i`.
      .mem_rvalid_i(AXI4_ADAP_inf_w.data_rvalid),
      /// See `axi_to_mem`, port `mem_rdata_i`.
      .mem_rdata_i(AXI4_ADAP_inf_w.data_rdata)
    );
    */

    typedef logic [AXI_ID_WIDTH-1:0]     id_t;
    typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
    typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
    typedef logic [AXI_USER_WIDTH-1:0]   user_t;
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
    `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
    `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
    
    req_t   req;
    resp_t  resp;
    
    `AXI_ASSIGN_TO_REQ(req, AXI4_slave)
    `AXI_ASSIGN_FROM_RESP(AXI4_slave, resp)
    /*
    axi_to_mem #(
        /// See `axi_to_mem`, parameter `AddrWidth`.
        .AddrWidth     ( AXI_ADDR_WIDTH),
        /// See `axi_to_mem`, parameter `DataWidth`.
        .DataWidth     ( AXI_DATA_WIDTH),
        /// AXI4+ATOP ID width.
        .IdWidth       ( AXI_ID_WIDTH),
        /// See `axi_to_mem`, parameter `NumBanks`.
        .NumBanks      ( 32'd1),
        /// See `axi_to_mem`, parameter `BufDepth`.
        .BufDepth      ( 32'd1),
        /// Hide write requests if the strb == '0
        .HideStrb      ( 1'b1),
        /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
        .OutFifoDepth ( 32'd1),
        
        .axi_req_t    ( req_t          ),
        .axi_resp_t   ( resp_t         )
    ) i_axi_to_mem (
        .clk_i(clk),
        .rst_ni(~reset),
        .busy_o(),
        .axi_req_i  ( req  ),
        .axi_resp_o ( resp ),
        
        .mem_req_o(AXI4_ADAP_inf_w.data_req),
        /// See `axi_to_mem`, port `mem_gnt_i`.
        .mem_gnt_i(AXI4_ADAP_inf_w.data_gnt),
        /// See `axi_to_mem`, port `mem_addr_o`.
        .mem_addr_o(AXI4_ADAP_inf_w.data_addr),
        /// See `axi_to_mem`, port `mem_wdata_o`.
        .mem_wdata_o(AXI4_ADAP_inf_w.data_wdata),
        /// See `axi_to_mem`, port `mem_strb_o`.
        .mem_strb_o(AXI4_ADAP_inf_w.data_be),
        /// See `axi_to_mem`, port `mem_atop_o`.
        .mem_atop_o(),
        /// See `axi_to_mem`, port `mem_we_o`.
        .mem_we_o(AXI4_ADAP_inf_w.data_we),
        /// See `axi_to_mem`, port `mem_rvalid_i`.
        .mem_rvalid_i(AXI4_ADAP_inf_w.data_rvalid),
        /// See `axi_to_mem`, port `mem_rdata_i`.
        .mem_rdata_i(AXI4_ADAP_inf_w.data_rdata)
    );
    */
    axi_to_detailed_mem #(
        .axi_req_t    ( req_t    ),
        .axi_resp_t   ( resp_t   ),
        .AddrWidth    ( AXI_ADDR_WIDTH    ),
        .DataWidth    ( AXI_DATA_WIDTH    ),
        .IdWidth      ( AXI_ID_WIDTH      ),
        .UserWidth    ( AXI_USER_WIDTH    ),
        .NumBanks     ( 32'd1     ),
        .BufDepth     ( 32'd1     ),
        .HideStrb     (  1'd0     ),
        .OutFifoDepth ( 32'd1 )
    ) i_axi_to_detailed_mem (
        .clk_i(clk),
        .rst_ni(~reset),
        .busy_o(),
        .axi_req_i    ( req     ),
        .axi_resp_o   ( resp    ),
        .mem_lock_o   (),
        .mem_id_o     (),
        .mem_user_o   (),
        .mem_cache_o  (),
        .mem_prot_o   (),
        .mem_qos_o    (),
        .mem_region_o (),
        .mem_err_i    ('0),
        .mem_exokay_i ('0),
        
        .mem_req_o(AXI4_ADAP_inf_w.data_req),
        /// See `axi_to_mem`, port `mem_gnt_i`.
        .mem_gnt_i(AXI4_ADAP_inf_w.data_gnt),
        /// See `axi_to_mem`, port `mem_addr_o`.
        .mem_addr_o(AXI4_ADAP_inf_w.data_addr),
        /// See `axi_to_mem`, port `mem_wdata_o`.
        .mem_wdata_o(AXI4_ADAP_inf_w.data_wdata),
        /// See `axi_to_mem`, port `mem_strb_o`.
        .mem_strb_o(AXI4_ADAP_inf_w.data_be),
        /// See `axi_to_mem`, port `mem_atop_o`.
        .mem_atop_o(),
        /// See `axi_to_mem`, port `mem_we_o`.
        .mem_we_o(AXI4_ADAP_inf_w.data_we),
        /// See `axi_to_mem`, port `mem_rvalid_i`.
        .mem_rvalid_i(AXI4_ADAP_inf_w.data_rvalid),
        /// See `axi_to_mem`, port `mem_rdata_i`.
        .mem_rdata_i(AXI4_ADAP_inf_w.data_rdata)
    );
    
    data_memory
    #(
        .SIZE_IN_KB(DATA_MEM_SIZE_IN_KB)
    )
    DATA_MEMORY
    (
        .clk_i(clk),
        .cv32_data_inf_i(AXI4_ADAP_inf_w)
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
            
            AXI4_slave.w_valid <= 1;
            AXI4_slave.w_data  <= data;
            AXI4_slave.w_strb  <= {AXI_DATA_WIDTH/8{1'b1}}; // write all bytes
            AXI4_slave.w_last  <= 1;
            AXI4_slave.w_user  <= 0;
    
            // Wait for aw_ready
            wait (AXI4_slave.aw_ready);
            @(posedge clk);
            AXI4_slave.aw_valid <= 0;
    
            // Write Data Channel
            
    
            // Wait for w_ready
            wait (AXI4_slave.w_ready);
            @(posedge clk);
            AXI4_slave.w_valid <= 0;
    
            // Write Response Channel
            wait (AXI4_slave.b_valid);
            AXI4_slave.b_ready <= 1;
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
    
    initial begin
        repeat(5) @(posedge clk);
        
        AXI4_WRITE(32'h0000_0000, 32'hdeaddead);
        
        repeat(5) @(posedge clk);
        $finish;
    end

endmodule
