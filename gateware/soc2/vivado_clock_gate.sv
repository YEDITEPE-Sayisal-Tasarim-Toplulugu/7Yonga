`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 16.05.2025 19:52:46
// Design Name: 
// Module Name: cv32e40p_clock_gate
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

module vivado_clock_gate (
    input  logic clk_i,
    input  logic en_i,
    input  logic scan_cg_en_i,
    output logic clk_o
);
  logic clock_enable = en_i | scan_cg_en_i;

  BUFGCE #(
    .CE_TYPE("SYNC"),            // ASYNC, HARDSYNC, SYNC
    .IS_CE_INVERTED(1'b0),       // Programmable inversion on CE
    .IS_I_INVERTED(1'b0),        // Programmable inversion on I
    .SIM_DEVICE("VERSAL_PRIME")  // VERSAL_PRIME, VERSAL_PRIME_ES1
  ) BUFGCE_inst (
    .O  ( clk_o           ),   // 1-bit output: Buffer
    .CE ( clock_enable    ), // 1-bit input: Buffer enable
    .I  ( clk_i           )    // 1-bit input: Buffer
  );

endmodule  // vivado_clock_gate
