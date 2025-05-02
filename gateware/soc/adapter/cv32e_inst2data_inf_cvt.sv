`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.04.2025 11:42:14
// Design Name: 
// Module Name: cv32e_inst2data_inf_cvt
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

`include "soc_interface_list.svh"

module cv32e_inst2data_inf_cvt
    (
        input CORE_INST_INF_M2S inst_slave_inf_m2s,
        output CORE_INST_INF_S2M inst_slave_inf_s2m,
        
        input CORE_DATA_INF_S2M data_master_inf_s2m,
        output CORE_DATA_INF_M2S data_master_inf_m2s
    );
    
    always_comb begin
        data_master_inf_m2s.data_addr = inst_slave_inf_m2s.instr_addr;
        data_master_inf_m2s.data_req = inst_slave_inf_m2s.instr_req;
        data_master_inf_m2s.data_we = 0;
        data_master_inf_m2s.data_be = 0;
        data_master_inf_m2s.data_wdata = 0;
        
        inst_slave_inf_s2m.instr_gnt = data_master_inf_s2m.data_gnt;
        inst_slave_inf_s2m.instr_rvalid = data_master_inf_s2m.data_rvalid;
        inst_slave_inf_s2m.instr_rdata = data_master_inf_s2m.data_rdata;
    end
    
endmodule




















