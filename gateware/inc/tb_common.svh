// M. Furkan UZUN

`ifndef __TB_COMMON_SVH__
`define __TB_COMMON_SVH__
    
`define CLK    clk
`define RST    resetn

`define SIM_CLK_RST(_p, _r, _c) \
    logic `CLK, `RST, sim_ready; \
    always #(_p/2) `CLK=~`CLK; \
    initial begin \
        `CLK=1'b0; \
        sim_ready = 1'b0; \
        @(negedge `CLK); \
        `RST = 1'b0; \
        repeat (_r) @(negedge `CLK); \
        `RST = 1'b1; \
        sim_ready = 1'b1; \
        repeat (_c - _r) @(posedge `CLK); \
        $display("[SIM] done."); \
        $finish; \
    end

`define CYCLE           @(posedge `CLK); #(1ps);
`define CYCLEN(_c)      repeat(_c) @(posedge `CLK); #(1ps);
`define WAIT_SIM        wait (sim_ready == 1'b1);

`define COMPARE(_cond, _msg) \
    if (!(_cond)) begin \
        $display("COMPARE-ERROR: time: [%0t ps] (%s) failed! %0d", $time, `__FILE__, `__LINE__); \
        $display("  Condition : %s", `"(_cond)`"); \
        $display("  Message   : %s", _msg); \
        $finish; \
    end

`define SIM_STOP \
    $display("Simulation completed successfully!"); \
    $finish;

`endif //__TB_COMMON_SVH__

















