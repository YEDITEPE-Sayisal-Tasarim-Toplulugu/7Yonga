`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.05.2025 16:11:12
// Design Name: 
// Module Name: tb_soc_top
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


module tb_soc_top();

    localparam PROGRAM_SIZE = 1024;

    localparam T=10;
    logic clk, reset;
    always #(T/2) clk=~clk;
    initial begin
        clk=1'b0;
        reset=1'b1;
        #(T*5);
        reset='b0;
    end
    
    soc_top
    DUT
    (
        .clk_i(clk), 
        .reset_i(reset)
    );
    
    // Test Program
    logic [31:0] test_program [0:8*1024];
    
    initial begin
        // Bellek içeriğini yükle
        $display("Loading memory from file...");
        $readmemh("program.mem", test_program);
        
        for (integer i=0; i<PROGRAM_SIZE; i++) begin
            DUT.CORE_INSTR_CONTROLLER.INSTRUCTION_ROM.SOC_CONFG_SOFT.SOFT_ROM.MEM[i] = test_program[i];
        end
    end
    
    initial begin
        repeat(1000) @(posedge clk);
        $finish;
    end

endmodule











