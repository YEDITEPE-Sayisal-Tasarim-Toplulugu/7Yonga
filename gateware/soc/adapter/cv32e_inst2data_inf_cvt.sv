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
        CORE_INST_INF.Slave inst_slave_inf,
        CORE_DATA_INF.Master data_master_inf
    );
    
    always_comb begin
        data_master_inf.data_addr = inst_slave_inf.instr_addr;
        data_master_inf.data_req = inst_slave_inf.instr_req;
        data_master_inf.data_we = 0;
        data_master_inf.data_be = 0;
        data_master_inf.data_wdata = 0;
        
        inst_slave_inf.instr_gnt = data_master_inf.data_gnt;
        inst_slave_inf.instr_rvalid = data_master_inf.data_rvalid;
        inst_slave_inf.instr_rdata = data_master_inf.data_rdata;
    end
    
endmodule




















