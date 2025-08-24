// Copyright 2025 Yeditepe Üniversitesi Sayısal Tasarım Topluluğu.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       M. Furkan UZUN - @mfu                                      //
//                                                                            //
//                                                                            //
// Design Name:    MEMORY MODELS                                              //
// Project Name:   7Yonga                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Mikrodenetleyici tasarımında kullanılacak bellek modelleri //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps

module memory_model_rom
    #(parameter
            WORD_SIZE_BITS = 32,
            SIZE_IN_BYTE = 1024
    )
    (
        input clk_i,

        input logic [$clog2((SIZE_IN_BYTE*8)/WORD_SIZE_BITS) : 0] read_addr_i,
        output logic [WORD_SIZE_BITS-1 : 0] read_data_o
    );

    localparam DEPTH = (SIZE_IN_BYTE*8)/WORD_SIZE_BITS;

    logic [WORD_SIZE_BITS-1 : 0] MEM [0:DEPTH-1];

    always_ff @(posedge clk_i) begin
        read_data_o <= MEM[read_addr_i[$clog2(DEPTH) : 0]];
    end

    ////////////////////////////////////////////////////////////////////////////////////
    //                                   ASSERTIONS                                   //
    ////////////////////////////////////////////////////////////////////////////////////

    // Assertion: read_addr_i must be within range
    property read_address_within_range;
        @(posedge clk_i)
        read_addr_i < DEPTH;
    endproperty

    assert property (read_address_within_range)
        else $error("read_addr_i (%0d) is out of range [0, %0d)", read_addr_i, DEPTH);

endmodule

module memory_model_soft
    #(parameter
        WORD_SIZE_BYTE = 4,
        SIZE_IN_KB = 8
    )
    (
        input logic clka,

        input logic ena,
        input logic [$clog2((SIZE_IN_KB*1024)/WORD_SIZE_BYTE) : 0] addra,

        input logic [WORD_SIZE_BYTE-1:0] wea,
        input logic [WORD_SIZE_BYTE*8-1:0] dina,

        output logic [WORD_SIZE_BYTE*8-1:0] douta
    );

    localparam DEPTH = (SIZE_IN_KB*1024)/WORD_SIZE_BYTE;

    logic [WORD_SIZE_BYTE*8-1 : 0] MEM [0:DEPTH-1];
    
    initial $readmemh("C:/Users/mhfur/Desktop/github_cloneS/7Yonga/firmware/program1_basic/BUILD/program.mem", MEM);
    
    logic [$clog2((SIZE_IN_KB*1024)/WORD_SIZE_BYTE) : 0] opAddr_w;
    assign opAddr_w = addra[$clog2((SIZE_IN_KB*1024)/WORD_SIZE_BYTE) : 0];

    always_ff @(posedge clka) begin
        if (ena) begin
            for (integer i=0; i<WORD_SIZE_BYTE; i++) begin
                if (wea[i]) begin
                    MEM[opAddr_w][i*8 +: 8] <= dina[i*8 +: 8];
                end
            end
        end

        if (ena & ~(|wea)) begin
            douta <= MEM[opAddr_w];
        end
    end

    ////////////////////////////////////////////////////////////////////////////////////
    //                                   ASSERTIONS                                   //
    ////////////////////////////////////////////////////////////////////////////////////
    // Assertion: addra must be within valid range
    /*
    property addr_within_range;
        @(posedge clka)
        (!ena) or (addra < DEPTH);
    endproperty

    assert property (addr_within_range)
        else $error("addra (%0d) is out of valid range [0, %0d)", addra, DEPTH);
    */

endmodule
