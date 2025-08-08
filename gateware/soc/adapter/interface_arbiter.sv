`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:55:56
// Design Name: 
// Module Name: interface_arbiter
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

module interface_arbiter
    #(parameter
            IN_COUNT = 2,
            IN_COUNT_LOG = ((IN_COUNT%2 == 0) ? $clog2(IN_COUNT) : $clog2(IN_COUNT) + 1)
    )
    (
        input logic clk_i, reset_i,
        
        input logic [IN_COUNT-1:0] valid_list_i,
        output logic [IN_COUNT_LOG-1:0] sel_o
    );
    
    logic [IN_COUNT-1:0] arbiter_rr_used_r, arbiter_rr_used_w;
    logic [IN_COUNT-1:0] used_list_w, avaliable_list_w, search_list_w;
    
    logic found_w;
    logic [IN_COUNT_LOG-1:0] sel_w;
    
    always_ff @(posedge clk_i, posedge reset_i) begin
        if (reset_i) begin
            arbiter_rr_used_r <= 0;
        end else begin
            arbiter_rr_used_r <= arbiter_rr_used_w;
        end
    end
    
    always_comb begin
        used_list_w = (&arbiter_rr_used_r) ? 0 : arbiter_rr_used_r;
        
        avaliable_list_w = (~used_list_w & valid_list_i);
        
        if (~(|avaliable_list_w)) begin
            search_list_w = valid_list_i;
        end else begin
            search_list_w = avaliable_list_w;
        end
        
        found_w = 1'b0;
        sel_w = 'd0;
        for (integer i=0; i<IN_COUNT; i++) begin
            if (search_list_w[i]) begin
                found_w = 1'b1;
                sel_w = i[IN_COUNT_LOG-1:0];
            end
        end
        
        arbiter_rr_used_w = arbiter_rr_used_r;
        if (found_w) begin
            arbiter_rr_used_w[sel_w] = 1'b1;
        end
        
        sel_o = sel_w;
    end
    
endmodule


















