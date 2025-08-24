`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 16.08.2025 12:45:39
// Design Name: 
// Module Name: vivado_iobuf
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

module vivado_iobuf(
    input wire I,
    input wire T,
    output wire O,
    inout wire IO
);

   // IOBUF: Single-ended Bi-directional Buffer
   //        All devices
   // Xilinx HDL Language Template, version 2023.2

   IOBUF #(
      .DRIVE(12), // Specify the output drive strength
      .IBUF_LOW_PWR("TRUE"),  // Low Power - "TRUE", High Performance = "FALSE"
      .IOSTANDARD("DEFAULT"), // Specify the I/O standard
      .SLEW("SLOW") // Specify the output slew rate
   ) IOBUF_inst (
      .O(O),     // Buffer output
      .IO(IO),   // Buffer inout port (connect directly to top-level port)
      .I(I),     // Buffer input
      .T(T)      // 3-state enable input, high=input, low=output
   );

   // End of IOBUF_inst instantiation

endmodule
