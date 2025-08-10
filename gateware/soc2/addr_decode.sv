`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09.08.2025 14:45:06
// Design Name: 
// Module Name: addr_decode
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



module addr_decode
    #(parameter type
            ID_TYPE         = logic,
            ADDR_TYPE       = logic,
            RULE_TYPE       = logic,
      parameter
            PORT_COUNT      = 2
    )
    (
        input RULE_TYPE     addr_rule_map_i     [0:PORT_COUNT-1],
        input ADDR_TYPE     addr_i,
        output logic        illegal_o,
        output ID_TYPE      selected_id_o
    );
    
    localparam PORT_ADDR_WIDTH = $clog2(PORT_COUNT);
    
    logic valid_w;
    logic [PORT_ADDR_WIDTH-1:0] sel_w;
    
    always_comb begin
        valid_w = 0;
        sel_w = 0;
        for (integer i=0; i<PORT_COUNT; i++) begin
            if (
                (addr_rule_map_i[i].start_addr <= addr_i) & 
                (addr_i <= addr_rule_map_i[i].end_addr)
            ) begin
                valid_w = 1'b1;
                sel_w = i[PORT_ADDR_WIDTH-1:0];
            end
        end
    end
    
    assign illegal_o        = ~valid_w;
    assign selected_id_o    = addr_rule_map_i[sel_w].id;
    
endmodule












