`timescale 1ns / 1ps

module qspi_master #(
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32
)(
    // Sistem sinyalleri
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // AXI4-Lite Slave Interface
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,
    
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [3:0]                  s_axi_wstrb,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,
    
    output logic [1:0]                  s_axi_bresp,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,
    
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,
    
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,
    
    // QSPI Interface
    output logic                        qspi_sclk_o,
    output logic                        qspi_cs_no,
    output logic [3:0]                  qspi_data_o,
    input  logic [3:0]                  qspi_data_i,
    output logic [3:0]                  qspi_data_oen   // Output enable (0: output, 1: input)
);

    // Register Offsets
    localparam REG_QSPI_CCR = 8'h00;
    localparam REG_QSPI_ADR = 8'h04;
    localparam REG_QSPI_DR0 = 8'h08;
    localparam REG_QSPI_DR1 = 8'h0C;
    localparam REG_QSPI_DR2 = 8'h10;
    localparam REG_QSPI_DR3 = 8'h14;
    localparam REG_QSPI_DR4 = 8'h18;
    localparam REG_QSPI_DR5 = 8'h1C;
    localparam REG_QSPI_DR6 = 8'h20;
    localparam REG_QSPI_DR7 = 8'h24;
    localparam REG_QSPI_STA = 8'h28;

    // QSPI_CCR Register Fields
    typedef struct packed {
        logic        clear_status;     // [31]
        logic [5:0]  prescaler;        // [30:25]
        logic [8:0]  data_length;      // [24:16]
        logic [4:0]  dummy_cycles;     // [15:11]
        logic        read_write;       // [10] - 0: read, 1: write
        logic [1:0]  data_mode;        // [9:8] - 00: no data, 01: x1, 10: x2, 11: x4
        logic [7:0]  instruction;      // [7:0]
    } qspi_ccr_t;

    // Internal Registers
    qspi_ccr_t  qspi_ccr;
    logic [23:0] qspi_adr;
    logic [31:0] qspi_dr[8];
    logic        transaction_complete;
    logic        busy;

    // State Machine
    typedef enum logic [3:0] {
        IDLE,
        SEND_INSTRUCTION,
        SEND_ADDRESS,
        DUMMY_CYCLES,
        TRANSFER_DATA,
        WAIT_COMPLETE
    } state_t;

    state_t current_state, next_state;

    // Internal signals
    logic        start_transaction;
    logic [5:0]  prescaler_cnt;
    logic        sclk_en;
    logic        sclk_posedge;
    logic        sclk_negedge;
    logic [2:0]  bit_cnt;
    logic [7:0]  byte_cnt;
    logic [4:0]  dummy_cnt;
    logic [8:0]  data_cnt;
    logic [7:0]  shift_reg_tx;
    logic [7:0]  shift_reg_rx;
    logic [2:0]  addr_byte_cnt;
    
    // AXI4-Lite Interface Logic
    logic        aw_handshake;
    logic        w_handshake;
    logic        ar_handshake;
    logic        write_enable;
    logic        read_enable;
    logic [7:0]  write_addr;
    logic [7:0]  read_addr;
    
    assign aw_handshake = s_axi_awvalid && s_axi_awready;
    assign w_handshake = s_axi_wvalid && s_axi_wready;
    assign ar_handshake = s_axi_arvalid && s_axi_arready;
    
    // Write Address Channel
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            s_axi_awready <= 1'b0;
            write_addr <= '0;
        end else begin
            if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid) begin
                s_axi_awready <= 1'b1;
                write_addr <= s_axi_awaddr[7:0];
            end else begin
                s_axi_awready <= 1'b0;
            end
        end
    end
    
    // Write Data Channel
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            s_axi_wready <= 1'b0;
        end else begin
            if (!s_axi_wready && s_axi_wvalid && s_axi_awvalid) begin
                s_axi_wready <= 1'b1;
            end else begin
                s_axi_wready <= 1'b0;
            end
        end
    end
    
    assign write_enable = aw_handshake && w_handshake;
    
    // Write Response Channel
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            s_axi_bvalid <= 1'b0;
            s_axi_bresp <= 2'b00;
        end else begin
            if (write_enable && !s_axi_bvalid) begin
                s_axi_bvalid <= 1'b1;
                s_axi_bresp <= 2'b00; // OKAY
            end else if (s_axi_bready && s_axi_bvalid) begin
                s_axi_bvalid <= 1'b0;
            end
        end
    end
    
    // Read Address Channel
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            s_axi_arready <= 1'b0;
            read_addr <= '0;
        end else begin
            if (!s_axi_arready && s_axi_arvalid) begin
                s_axi_arready <= 1'b1;
                read_addr <= s_axi_araddr[7:0];
            end else begin
                s_axi_arready <= 1'b0;
            end
        end
    end
    
    assign read_enable = ar_handshake;
    
    // Read Data Channel
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            s_axi_rvalid <= 1'b0;
            s_axi_rresp <= 2'b00;
            s_axi_rdata <= '0;
        end else begin
            if (read_enable && !s_axi_rvalid) begin
                s_axi_rvalid <= 1'b1;
                s_axi_rresp <= 2'b00; // OKAY
                
                case (read_addr)
                    REG_QSPI_CCR: s_axi_rdata <= qspi_ccr;
                    REG_QSPI_ADR: s_axi_rdata <= {8'h00, qspi_adr};
                    REG_QSPI_DR0: s_axi_rdata <= qspi_dr[0];
                    REG_QSPI_DR1: s_axi_rdata <= qspi_dr[1];
                    REG_QSPI_DR2: s_axi_rdata <= qspi_dr[2];
                    REG_QSPI_DR3: s_axi_rdata <= qspi_dr[3];
                    REG_QSPI_DR4: s_axi_rdata <= qspi_dr[4];
                    REG_QSPI_DR5: s_axi_rdata <= qspi_dr[5];
                    REG_QSPI_DR6: s_axi_rdata <= qspi_dr[6];
                    REG_QSPI_DR7: s_axi_rdata <= qspi_dr[7];
                    REG_QSPI_STA: s_axi_rdata <= {30'h0, busy, transaction_complete};
                    default: s_axi_rdata <= '0;
                endcase
            end else if (s_axi_rvalid && s_axi_rready) begin
                s_axi_rvalid <= 1'b0;
            end
        end
    end
    
    // Register Write Logic
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            qspi_ccr <= '0;
            qspi_adr <= '0;
            for (int i = 0; i < 8; i++) begin
                qspi_dr[i] <= '0;
            end
            start_transaction <= 1'b0;
        end else begin
            start_transaction <= 1'b0;
            
            if (write_enable) begin
                case (write_addr)
                    REG_QSPI_CCR: begin
                        qspi_ccr <= s_axi_wdata;
                        start_transaction <= 1'b1;
                    end
                    REG_QSPI_ADR: qspi_adr <= s_axi_wdata[23:0];
                    REG_QSPI_DR0: qspi_dr[0] <= s_axi_wdata;
                    REG_QSPI_DR1: qspi_dr[1] <= s_axi_wdata;
                    REG_QSPI_DR2: qspi_dr[2] <= s_axi_wdata;
                    REG_QSPI_DR3: qspi_dr[3] <= s_axi_wdata;
                    REG_QSPI_DR4: qspi_dr[4] <= s_axi_wdata;
                    REG_QSPI_DR5: qspi_dr[5] <= s_axi_wdata;
                    REG_QSPI_DR6: qspi_dr[6] <= s_axi_wdata;
                    REG_QSPI_DR7: qspi_dr[7] <= s_axi_wdata;
                endcase
            end
            
            // Clear status register
            if (qspi_ccr.clear_status) begin
                qspi_ccr.clear_status <= 1'b0;
            end
        end
    end
    
    // Clock Prescaler
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            prescaler_cnt <= '0;
            sclk_en <= 1'b0;
        end else begin
            if (current_state == IDLE) begin
                prescaler_cnt <= '0;
                sclk_en <= 1'b0;
            end else begin
                if (prescaler_cnt == qspi_ccr.prescaler) begin
                    prescaler_cnt <= '0;
                    sclk_en <= 1'b1;
                end else begin
                    prescaler_cnt <= prescaler_cnt + 1'b1;
                    sclk_en <= 1'b0;
                end
            end
        end
    end
    
    // SCLK Generation (Mode 0: CPOL=0, CPHA=0)
    logic sclk_int;
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            sclk_int <= 1'b0;
        end else begin
            if (current_state == IDLE) begin
                sclk_int <= 1'b0;
            end else if (sclk_en) begin
                sclk_int <= ~sclk_int;
            end
        end
    end
    
    assign sclk_posedge = sclk_en && !sclk_int;
    assign sclk_negedge = sclk_en && sclk_int;
    assign qspi_sclk_o = sclk_int;
    
    // State Machine
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    
    always_comb begin
        next_state = current_state;
        
        case (current_state)
            IDLE: begin
                if (start_transaction) begin
                    next_state = SEND_INSTRUCTION;
                end
            end
            
            SEND_INSTRUCTION: begin
                if (sclk_negedge && bit_cnt == 3'd7) begin
                    if (|qspi_adr) begin
                        next_state = SEND_ADDRESS;
                    end else if (qspi_ccr.dummy_cycles != 5'd0) begin
                        next_state = DUMMY_CYCLES;
                    end else if (qspi_ccr.data_mode != 2'b00) begin
                        next_state = TRANSFER_DATA;
                    end else begin
                        next_state = WAIT_COMPLETE;
                    end
                end
            end
            
            SEND_ADDRESS: begin
                if (sclk_negedge && bit_cnt == 3'd7 && addr_byte_cnt == 3'd2) begin
                    if (qspi_ccr.dummy_cycles != 5'd0) begin
                        next_state = DUMMY_CYCLES;
                    end else if (qspi_ccr.data_mode != 2'b00) begin
                        next_state = TRANSFER_DATA;
                    end else begin
                        next_state = WAIT_COMPLETE;
                    end
                end
            end
            
            DUMMY_CYCLES: begin
                if (sclk_negedge && dummy_cnt == qspi_ccr.dummy_cycles - 1'b1) begin
                    if (qspi_ccr.data_mode != 2'b00) begin
                        next_state = TRANSFER_DATA;
                    end else begin
                        next_state = WAIT_COMPLETE;
                    end
                end
            end
            
            TRANSFER_DATA: begin
                if (sclk_negedge && data_cnt > qspi_ccr.data_length) begin
                    next_state = WAIT_COMPLETE;
                end
            end
            
            WAIT_COMPLETE: begin
                if (sclk_negedge) begin
                    next_state = IDLE;
                end
            end
            
            default: next_state = IDLE;
        endcase
    end
    
    // Control Logic
    always_ff @(posedge clk_i) begin
        if (!rst_ni) begin
            qspi_cs_no <= 1'b1;
            qspi_data_o <= 4'h0;
            qspi_data_oen <= 4'hF;
            bit_cnt <= 3'd0;
            byte_cnt <= 8'd0;
            dummy_cnt <= 5'd0;
            data_cnt <= 9'd0;
            shift_reg_tx <= 8'h00;
            shift_reg_rx <= 8'h00;
            addr_byte_cnt <= 3'd0;
            transaction_complete <= 1'b0;
            busy <= 1'b0;
        end else begin
            // Clear transaction complete flag
            if (qspi_ccr.clear_status) begin
                transaction_complete <= 1'b0;
            end
            
            case (current_state)
                IDLE: begin
                    qspi_cs_no <= 1'b1;
                    qspi_data_oen <= 4'hF;
                    bit_cnt <= 3'd0;
                    byte_cnt <= 8'd0;
                    dummy_cnt <= 5'd0;
                    data_cnt <= 9'd0;
                    addr_byte_cnt <= 3'd0;
                    busy <= 1'b0;
                    shift_reg_tx <= 8'h00;
                    shift_reg_rx <= 8'h00;
                    
                    if (start_transaction) begin
                        qspi_cs_no <= 1'b0;
                        shift_reg_tx <= qspi_ccr.instruction;
                        busy <= 1'b1;
                    end
                end
                
                SEND_INSTRUCTION: begin
                    // Always send instruction in x1 mode
                    qspi_data_oen <= 4'hE; // Only data[0] is output
                    
                    if (sclk_negedge) begin
                        qspi_data_o[0] <= shift_reg_tx[7];
                        shift_reg_tx <= {shift_reg_tx[6:0], 1'b0};
                        bit_cnt <= bit_cnt + 1'b1;
                        
                        if (bit_cnt == 3'd7) begin
                            bit_cnt <= 3'd0;
                            if (|qspi_adr) begin
                                shift_reg_tx <= qspi_adr[23:16];
                            end else if (qspi_ccr.dummy_cycles == 5'd0 && qspi_ccr.data_mode != 2'b00) begin
                                // Prepare first data byte if going directly to TRANSFER_DATA
                                if (qspi_ccr.read_write) begin
                                    // Write: load first byte
                                    shift_reg_tx <= qspi_dr[0][7:0];
                                end else begin
                                    // Read: clear shift register
                                    shift_reg_rx <= 8'h00;
                                end
                            end
                        end
                    end
                end
                
                SEND_ADDRESS: begin
                    // Always send address in x1 mode
                    qspi_data_oen <= 4'hE; // Only data[0] is output
                    
                    if (sclk_negedge) begin
                        qspi_data_o[0] <= shift_reg_tx[7];
                        shift_reg_tx <= {shift_reg_tx[6:0], 1'b0};
                        bit_cnt <= bit_cnt + 1'b1;
                        
                        if (bit_cnt == 3'd7) begin
                            bit_cnt <= 3'd0;
                            addr_byte_cnt <= addr_byte_cnt + 1'b1;
                            
                            case (addr_byte_cnt)
                                3'd0: shift_reg_tx <= qspi_adr[15:8];
                                3'd1: shift_reg_tx <= qspi_adr[7:0];
                                3'd2: begin
                                    // Prepare for next state
                                    if (qspi_ccr.dummy_cycles == 5'd0 && qspi_ccr.data_mode != 2'b00) begin
                                        if (qspi_ccr.read_write) begin
                                            // Write: load first byte
                                            shift_reg_tx <= qspi_dr[0][7:0];
                                        end else begin
                                            // Read: clear shift register
                                            shift_reg_rx <= 8'h00;
                                        end
                                    end else begin
                                        shift_reg_tx <= 8'h00;
                                    end
                                end
                                default: shift_reg_tx <= 8'h00;
                            endcase
                        end
                    end
                end
                
                DUMMY_CYCLES: begin
                    // Configure data pins based on data mode for dummy cycles
                    case (qspi_ccr.data_mode)
                        2'b01: qspi_data_oen <= 4'hE; // x1 mode
                        2'b10: qspi_data_oen <= 4'hC; // x2 mode
                        2'b11: qspi_data_oen <= 4'h0; // x4 mode
                        default: qspi_data_oen <= 4'hF;
                    endcase
                    
                    if (sclk_negedge) begin
                        dummy_cnt <= dummy_cnt + 1'b1;
                        
                        // Prepare for next state if this is the last dummy cycle
                        if (dummy_cnt == qspi_ccr.dummy_cycles - 1'b1 && qspi_ccr.data_mode != 2'b00) begin
                            if (qspi_ccr.read_write) begin
                                // Write: load first byte
                                shift_reg_tx <= qspi_dr[0][7:0];
                            end else begin
                                // Read: clear shift register
                                shift_reg_rx <= 8'h00;
                            end
                        end
                    end
                end
                
                TRANSFER_DATA: begin
                    // Configure data pins based on read/write and data mode
                    if (qspi_ccr.read_write) begin
                        // Write operation
                        case (qspi_ccr.data_mode)
                            2'b01: qspi_data_oen <= 4'hE; // x1 mode
                            2'b10: qspi_data_oen <= 4'hC; // x2 mode
                            2'b11: qspi_data_oen <= 4'h0; // x4 mode
                            default: qspi_data_oen <= 4'hF;
                        endcase
                    end else begin
                        // Read operation - all pins are inputs
                        qspi_data_oen <= 4'hF;
                    end
                    
                    // Data transfer logic
                    if (qspi_ccr.read_write) begin
                        // Write operation
                        // Load byte at the beginning of each byte transfer
                        if (bit_cnt == 3'd0 && data_cnt <= qspi_ccr.data_length) begin
                            // Simplified byte selection for better synthesis
                            case (byte_cnt)
                                8'd0:  shift_reg_tx <= qspi_dr[0][7:0];
                                8'd1:  shift_reg_tx <= qspi_dr[0][15:8];
                                8'd2:  shift_reg_tx <= qspi_dr[0][23:16];
                                8'd3:  shift_reg_tx <= qspi_dr[0][31:24];
                                8'd4:  shift_reg_tx <= qspi_dr[1][7:0];
                                8'd5:  shift_reg_tx <= qspi_dr[1][15:8];
                                8'd6:  shift_reg_tx <= qspi_dr[1][23:16];
                                8'd7:  shift_reg_tx <= qspi_dr[1][31:24];
                                8'd8:  shift_reg_tx <= qspi_dr[2][7:0];
                                8'd9:  shift_reg_tx <= qspi_dr[2][15:8];
                                8'd10: shift_reg_tx <= qspi_dr[2][23:16];
                                8'd11: shift_reg_tx <= qspi_dr[2][31:24];
                                8'd12: shift_reg_tx <= qspi_dr[3][7:0];
                                8'd13: shift_reg_tx <= qspi_dr[3][15:8];
                                8'd14: shift_reg_tx <= qspi_dr[3][23:16];
                                8'd15: shift_reg_tx <= qspi_dr[3][31:24];
                                8'd16: shift_reg_tx <= qspi_dr[4][7:0];
                                8'd17: shift_reg_tx <= qspi_dr[4][15:8];
                                8'd18: shift_reg_tx <= qspi_dr[4][23:16];
                                8'd19: shift_reg_tx <= qspi_dr[4][31:24];
                                8'd20: shift_reg_tx <= qspi_dr[5][7:0];
                                8'd21: shift_reg_tx <= qspi_dr[5][15:8];
                                8'd22: shift_reg_tx <= qspi_dr[5][23:16];
                                8'd23: shift_reg_tx <= qspi_dr[5][31:24];
                                8'd24: shift_reg_tx <= qspi_dr[6][7:0];
                                8'd25: shift_reg_tx <= qspi_dr[6][15:8];
                                8'd26: shift_reg_tx <= qspi_dr[6][23:16];
                                8'd27: shift_reg_tx <= qspi_dr[6][31:24];
                                8'd28: shift_reg_tx <= qspi_dr[7][7:0];
                                8'd29: shift_reg_tx <= qspi_dr[7][15:8];
                                8'd30: shift_reg_tx <= qspi_dr[7][23:16];
                                8'd31: shift_reg_tx <= qspi_dr[7][31:24];
                                default: shift_reg_tx <= 8'h00;
                            endcase
                        end
                        
                        if (sclk_negedge) begin
                            case (qspi_ccr.data_mode)
                                2'b01: begin // x1 mode
                                    qspi_data_o[0] <= shift_reg_tx[7];
                                    shift_reg_tx <= {shift_reg_tx[6:0], 1'b0};
                                    bit_cnt <= bit_cnt + 1'b1;
                                end
                                2'b10: begin // x2 mode
                                    qspi_data_o[1:0] <= shift_reg_tx[7:6];
                                    shift_reg_tx <= {shift_reg_tx[5:0], 2'b00};
                                    bit_cnt <= bit_cnt + 2'd2;
                                end
                                2'b11: begin // x4 mode
                                    qspi_data_o[3:0] <= shift_reg_tx[7:4];
                                    shift_reg_tx <= {shift_reg_tx[3:0], 4'h0};
                                    bit_cnt <= bit_cnt + 3'd4;
                                end
                                default: ; // Invalid data mode
                            endcase
                            
                            if ((qspi_ccr.data_mode == 2'b01 && bit_cnt == 3'd7) ||
                                (qspi_ccr.data_mode == 2'b10 && bit_cnt >= 3'd6) ||
                                (qspi_ccr.data_mode == 2'b11 && bit_cnt >= 3'd4)) begin
                                bit_cnt <= 3'd0;
                                if (data_cnt <= qspi_ccr.data_length) begin
                                    byte_cnt <= byte_cnt + 1'b1;
                                    data_cnt <= data_cnt + 1'b1;
                                end
                            end
                        end
                    end else begin
                        // Read operation
                        if (sclk_posedge) begin
                            case (qspi_ccr.data_mode)
                                2'b01: begin // x1 mode - read from pin 1
                                    shift_reg_rx <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                    bit_cnt <= bit_cnt + 1'b1;
                                    
                                    // Store byte when complete (after 8 bits received)
                                    if (bit_cnt == 3'd7) begin
                                        bit_cnt <= 3'd0;
                                        
                                        // Store the complete byte with the last bit
                                        case (byte_cnt)
                                            8'd0:  qspi_dr[0][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd1:  qspi_dr[0][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd2:  qspi_dr[0][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd3:  qspi_dr[0][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd4:  qspi_dr[1][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd5:  qspi_dr[1][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd6:  qspi_dr[1][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd7:  qspi_dr[1][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd8:  qspi_dr[2][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd9:  qspi_dr[2][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd10: qspi_dr[2][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd11: qspi_dr[2][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd12: qspi_dr[3][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd13: qspi_dr[3][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd14: qspi_dr[3][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd15: qspi_dr[3][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd16: qspi_dr[4][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd17: qspi_dr[4][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd18: qspi_dr[4][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd19: qspi_dr[4][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd20: qspi_dr[5][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd21: qspi_dr[5][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd22: qspi_dr[5][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd23: qspi_dr[5][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd24: qspi_dr[6][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd25: qspi_dr[6][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd26: qspi_dr[6][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd27: qspi_dr[6][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd28: qspi_dr[7][7:0]   <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd29: qspi_dr[7][15:8]  <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd30: qspi_dr[7][23:16] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                            8'd31: qspi_dr[7][31:24] <= {shift_reg_rx[6:0], qspi_data_i[1]};
                                        endcase
                                        
                                        data_cnt <= data_cnt + 1'b1;
                                        if (data_cnt < qspi_ccr.data_length) begin
                                            byte_cnt <= byte_cnt + 1'b1;
                                        end
                                    end
                                end
                                
                                2'b10: begin // x2 mode - read from pins 1:0
                                    shift_reg_rx <= {shift_reg_rx[5:0], qspi_data_i[1:0]};
                                    bit_cnt <= bit_cnt + 2'd2;
                                    
                                    if (bit_cnt >= 3'd6) begin
                                        bit_cnt <= 3'd0;
                                        
                                        // Store received byte
                                        case (byte_cnt)
                                            8'd0:  qspi_dr[0][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd1:  qspi_dr[0][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd2:  qspi_dr[0][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd3:  qspi_dr[0][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd4:  qspi_dr[1][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd5:  qspi_dr[1][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd6:  qspi_dr[1][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd7:  qspi_dr[1][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd8:  qspi_dr[2][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd9:  qspi_dr[2][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd10: qspi_dr[2][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd11: qspi_dr[2][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd12: qspi_dr[3][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd13: qspi_dr[3][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd14: qspi_dr[3][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd15: qspi_dr[3][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd16: qspi_dr[4][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd17: qspi_dr[4][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd18: qspi_dr[4][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd19: qspi_dr[4][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd20: qspi_dr[5][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd21: qspi_dr[5][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd22: qspi_dr[5][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd23: qspi_dr[5][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd24: qspi_dr[6][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd25: qspi_dr[6][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd26: qspi_dr[6][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd27: qspi_dr[6][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd28: qspi_dr[7][7:0]   <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd29: qspi_dr[7][15:8]  <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd30: qspi_dr[7][23:16] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                            8'd31: qspi_dr[7][31:24] <= (bit_cnt == 3'd6) ? {shift_reg_rx[5:0], qspi_data_i[1:0]} : shift_reg_rx;
                                        endcase
                                        
                                        data_cnt <= data_cnt + 1'b1;
                                        if (data_cnt < qspi_ccr.data_length) begin
                                            byte_cnt <= byte_cnt + 1'b1;
                                        end
                                    end
                                end
                                
                                2'b11: begin // x4 mode - read from pins 3:0
                                    shift_reg_rx <= {shift_reg_rx[3:0], qspi_data_i[3:0]};
                                    bit_cnt <= bit_cnt + 3'd4;
                                    
                                    if (bit_cnt >= 3'd4) begin
                                        bit_cnt <= 3'd0;
                                        
                                        // Store received byte
                                        case (byte_cnt)
                                            8'd0:  qspi_dr[0][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd1:  qspi_dr[0][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd2:  qspi_dr[0][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd3:  qspi_dr[0][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd4:  qspi_dr[1][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd5:  qspi_dr[1][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd6:  qspi_dr[1][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd7:  qspi_dr[1][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd8:  qspi_dr[2][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd9:  qspi_dr[2][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd10: qspi_dr[2][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd11: qspi_dr[2][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd12: qspi_dr[3][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd13: qspi_dr[3][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd14: qspi_dr[3][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd15: qspi_dr[3][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd16: qspi_dr[4][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd17: qspi_dr[4][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd18: qspi_dr[4][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd19: qspi_dr[4][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd20: qspi_dr[5][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd21: qspi_dr[5][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd22: qspi_dr[5][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd23: qspi_dr[5][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd24: qspi_dr[6][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd25: qspi_dr[6][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd26: qspi_dr[6][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd27: qspi_dr[6][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd28: qspi_dr[7][7:0]   <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd29: qspi_dr[7][15:8]  <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd30: qspi_dr[7][23:16] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                            8'd31: qspi_dr[7][31:24] <= (bit_cnt == 3'd4) ? {shift_reg_rx[3:0], qspi_data_i[3:0]} : shift_reg_rx;
                                        endcase
                                        
                                        data_cnt <= data_cnt + 1'b1;
                                        if (data_cnt < qspi_ccr.data_length) begin
                                            byte_cnt <= byte_cnt + 1'b1;
                                        end
                                    end
                                end
                            endcase
                        end
                    end
                end
                
                WAIT_COMPLETE: begin
                    if (sclk_negedge) begin
                        qspi_cs_no <= 1'b1;
                        transaction_complete <= 1'b1;
                        busy <= 1'b0;
                    end
                end
                
                default: begin
                    // Default case - should not happen
                    qspi_cs_no <= 1'b1;
                    qspi_data_oen <= 4'hF;
                    busy <= 1'b0;
                end
            endcase // current_state
        end
    end

endmodule