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

module cv32e40p_clock_gate 
  import soc_config_pkg::*;
(
    input  logic clk_i,
    input  logic en_i,
    input  logic scan_cg_en_i,
    output logic clk_o
);

if (soc_config_pkg::USE_CLOCK_GATE_TYPE == soc_config_pkg::VIVADOBUF) begin : SOC_VIVADO_BUFF_TYPE
  vivado_clock_gate clock_gate (
    clk_i,
    en_i,
    scan_cg_en_i,
    clk_o
  );
end else if (soc_config_pkg::USE_CLOCK_GATE_TYPE == soc_config_pkg::BYPASS) begin : SOC_BYPASS_BUFF_TYPE
  verilator_clock_gate clock_gate (
    clk_i,
    en_i,
    scan_cg_en_i,
    clk_o
  );
end

endmodule  // cv32e40p_clock_gate
