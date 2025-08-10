`timescale 1ns / 1ps

module roundrobin_arbiter
    #(parameter
            PORT_COUNT      = 8,
            PRIORTY_AT_0    = 1,
            
            PORT_ID_WIDTH   = $clog2(PORT_COUNT)
    )
    (
        input logic clk_i, reset_ni,
        
        input logic [PORT_COUNT-1:0]        port_ready_list_i,
        output logic [PORT_ID_WIDTH-1:0]    port_selected_id_o
    ); 
    
    logic [PORT_COUNT-1:0] used_list_r, used_list_w, valid_list_w;
    logic [PORT_ID_WIDTH-1:0]    port_selected_id_w;
    
    assign port_selected_id_o = port_selected_id_w;
    
    always_ff @(posedge clk_i, negedge reset_ni) begin
        if (~reset_ni) begin
            used_list_r <= 0;
        end else begin
            used_list_r <= used_list_w;
        end
    end
    
    always_comb begin
        used_list_w = used_list_r;
        
        if (&used_list_r) begin // hepsi tamamdır
            used_list_w = 0;
        end
        
        valid_list_w = ~used_list_w & port_ready_list_i;
        port_selected_id_w = 0; 
        
        if (PRIORTY_AT_0) begin
            for (integer i=PORT_COUNT-1; i>=0; i--) begin
                if (valid_list_w[i]) begin
                    port_selected_id_w = i[PORT_ID_WIDTH-1:0];
                end
            end
        end else begin
            for (integer i=0; i<PORT_COUNT; i++) begin
                if (valid_list_w[i]) begin
                    port_selected_id_w = i[PORT_ID_WIDTH-1:0];
                end
            end
        end
        
        if (port_ready_list_i[port_selected_id_w])
            used_list_w[port_selected_id_w] = 1'b1;
    end
    
endmodule

















