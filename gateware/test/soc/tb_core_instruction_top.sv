`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 18.05.2025 22:07:30
// Design Name: 
// Module Name: tb_core_instruction_top
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


module tb_core_instruction_top();

    localparam T=10;
    logic clk, reset;
    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        reset=1'b1;
        #(T*5);
        reset='b0;
    end

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
    
    CORE_INST_INF CORE_inst_inf_i();

    core_instruction_top
    #(
        .ROM_SIZE_IN_BYTE       ( 1024              ),
        .INST_MEM_SIZE_IN_KB    ( 8                 ),
            
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
        
        // Core Intsruction Interface
        .CORE_inst_inf_i(CORE_inst_inf_i),
        
        .slv(AXI4_slave)
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
        
        
        CORE_inst_inf_i.instr_addr = 'b0;
        CORE_inst_inf_i.instr_req = 'b0;
        CORE_inst_inf_i.instr_gnt = 'b0;
        CORE_inst_inf_i.instr_rvalid = 'b0;
        CORE_inst_inf_i.instr_rdata = 'b0;
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
            
            // Write Data Channel
            AXI4_slave.w_valid <= 1;
            AXI4_slave.w_data  <= data;
            AXI4_slave.w_strb  <= {AXI_DATA_WIDTH/8{1'b1}}; // write all bytes
            AXI4_slave.w_last  <= 1;
            AXI4_slave.w_user  <= 0;
    
            // Wait for aw_ready
            wait (AXI4_slave.aw_ready);
            @(posedge clk);
            AXI4_slave.aw_valid <= 0;
    
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
    
    task INST_READ;
        input  logic [31:0] addr;
        output logic [31:0] instr;
    
        begin
            // Request başlatılıyor
            @(posedge clk);
            CORE_inst_inf_i.instr_addr <= addr;
            CORE_inst_inf_i.instr_req  <= 1'b1;
    
            // instr_gnt verilene kadar beklenir
            wait (CORE_inst_inf_i.instr_gnt == 1'b1);
            @(posedge clk);
            CORE_inst_inf_i.instr_req <= 1'b0;
    
            // instr_rvalid beklenir
            wait (CORE_inst_inf_i.instr_rvalid == 1'b1);
            instr = CORE_inst_inf_i.instr_rdata;
    
            @(posedge clk);
        end
    endtask
    
    logic [31:0] CORE_inst_data;
    
    initial begin
        repeat(5) @(posedge clk);
        
        AXI4_WRITE((32'h2000_0000+8'h0C), 32'hdeaddead);
        INST_READ(32'h3000_0000, CORE_inst_data);
        
        repeat(5) @(posedge clk);
        $finish;
    end

endmodule

















