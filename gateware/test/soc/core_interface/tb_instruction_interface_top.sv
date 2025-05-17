`timescale 1ns / 1ps

`include "soc_configuration.svh"
`include "soc_interface_list.svh"
`include "soc_addr_rules.svh"

module tb_instruction_interface_top();

    parameter T=10;
    parameter RESET_DUR_=30;
    parameter SIM_MAX=T*100;

    parameter
            ROM_SIZE_IN_BYTE = 1024,
            INST_MEM_SIZE_IN_KB = 8;
            
      /// AXI4+ATOP ID width.
      parameter int unsigned ID_WIDTH       = 32'd8;
      /// AXI4+ATOP user width.
      parameter int unsigned USER_WIDTH     = 32'd8;
      
    logic clk, reset;

    CORE_INST_INF_M2S CORE_inst_inf_m2s;
    CORE_INST_INF_S2M CORE_inst_inf_s2m;
    
    AXI_BUS #(
      .AXI_ADDR_WIDTH(32),
      .AXI_DATA_WIDTH(64),
      .AXI_ID_WIDTH(ID_WIDTH),
      .AXI_USER_WIDTH(USER_WIDTH)
    ) slv();

    core_instruction_top
    #(
        .ROM_SIZE_IN_BYTE(ROM_SIZE_IN_BYTE),
        .INST_MEM_SIZE_IN_KB(INST_MEM_SIZE_IN_KB),
            
        /// AXI4+ATOP ID width.
        .ID_WIDTH       (ID_WIDTH),
        /// AXI4+ATOP user width.
        .USER_WIDTH     (USER_WIDTH)
    )
    DUT
    (
        .clk_i(clk), .reset_i(reset),
        
        // Core Intsruction Interface
        .CORE_inst_inf_m2s(CORE_inst_inf_m2s),
        .CORE_inst_inf_s2m(CORE_inst_inf_s2m),
        
        .slv(slv)
    );
    
    always #(T/2) clk=~clk;
    initial begin
        clk = 0;
        reset=1;
        #(RESET_DUR_);
        reset=0;
    end
    
    initial begin
        #(SIM_MAX);
        $display("Simulation is terminated.");
        $finish;
    end
    
    initial begin
        CORE_inst_inf_m2s.instr_addr = 0;
        CORE_inst_inf_m2s.instr_req  = 0;
        
        slv.aw_id = 0;
        slv.aw_addr = 0;
        slv.aw_len = 0;
        slv.aw_size = 0;
        slv.aw_burst = 0;
        slv.aw_lock = 0;
        slv.aw_cache = 0;
        slv.aw_prot = 0;
        slv.aw_qos = 0;
        slv.aw_region = 0;
        slv.aw_atop = 0;
        slv.aw_user = 0;
        slv.aw_valid = 0;
        
        slv.w_data = 0;
        slv.w_strb = 0;
        slv.w_last = 0;
        slv.w_user = 0;
        slv.w_valid = 0;
        
        slv.b_ready = 0;
        
        slv.ar_id = 0;
        slv.ar_addr = 0;
        slv.ar_len = 0;
        slv.ar_size = 0;
        slv.ar_burst = 0;
        slv.ar_lock = 0;
        slv.ar_cache = 0;
        slv.ar_prot = 0;
        slv.ar_qos = 0;
        slv.ar_region = 0;
        slv.ar_user = 0;
        slv.ar_valid = 0;
        slv.r_ready = 0;
        
        #(T*10);
        @(posedge clk);
        
        
        CORE_inst_inf_m2s.instr_addr = 32'h3000_0010;
        CORE_inst_inf_m2s.instr_req  = 1'b1;
        wait (CORE_inst_inf_s2m.instr_gnt == 1'b1);
        @(posedge clk);
        CORE_inst_inf_m2s.instr_req  = 1'b0;
        
        #(T*2);
        @(posedge clk);
        
        CORE_inst_inf_m2s.instr_addr = 32'h2000_0020;
        CORE_inst_inf_m2s.instr_req  = 1'b1;
        wait (CORE_inst_inf_s2m.instr_gnt == 1'b1);
        @(posedge clk);
        CORE_inst_inf_m2s.instr_req  = 1'b0;
    end

endmodule



















