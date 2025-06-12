module i2c_master (
    // Clock and reset signals
    input  logic        s_axi_aclk,
    input  logic        s_axi_aresetn,
    
    // AXI4-Lite Slave Interface
    // Write Address Channel
    input  logic [31:0] s_axi_awaddr,
    input  logic        s_axi_awvalid,
    output logic        s_axi_awready,
    
    // Write Data Channel
    input  logic [31:0] s_axi_wdata,
    input  logic [3:0]  s_axi_wstrb,
    input  logic        s_axi_wvalid,
    output logic        s_axi_wready,
    
    // Write Response Channel
    output logic [1:0]  s_axi_bresp,
    output logic        s_axi_bvalid,
    input  logic        s_axi_bready,
    
    // Read Address Channel
    input  logic [31:0] s_axi_araddr,
    input  logic        s_axi_arvalid,
    output logic        s_axi_arready,
    
    // Read Data Channel
    output logic [31:0] s_axi_rdata,
    output logic [1:0]  s_axi_rresp,
    output logic        s_axi_rvalid,
    input  logic        s_axi_rready,
    
    // I2C Interface
    input  logic        scl_i,
    output logic        scl_o,
    output logic        scl_oen,    // Output enable (active low)
    input  logic        sda_i,
    output logic        sda_o,
    output logic        sda_oen     // Output enable (active low)
);

    // Register addresses
    localparam I2C_NBY = 8'h00;  // Number of bytes register
    localparam I2C_ADR = 8'h04;  // Slave address register
    localparam I2C_RDR = 8'h08;  // Read data register
    localparam I2C_TDR = 8'h0C;  // Transmit data register
    localparam I2C_CFG = 8'h10;  // Configuration register
    
    // Clock divider for 400kHz from 100MHz
    localparam CLK_DIV = 16'd62;  // Actually 63 cycles, but 0-62 = 63 states
    
    // I2C state machine states
    typedef enum logic [3:0] {
        IDLE        = 4'b0000,
        START       = 4'b0001,
        SEND_ADDR   = 4'b0010,
        RECV_ACK    = 4'b0011,
        SEND_DATA   = 4'b0100,
        READ_DATA   = 4'b0101,
        SEND_ACK    = 4'b0110,
        STOP        = 4'b0111,
        ERROR       = 4'b1000
    } i2c_state_t;
    
    // Registers
    logic [31:0] i2c_nby_reg;    // Number of bytes (1-4)
    logic [31:0] i2c_adr_reg;    // 7-bit slave address
    logic [31:0] i2c_rdr_reg;    // Read data register
    logic [31:0] i2c_tdr_reg;    // Transmit data register
    logic [31:0] i2c_cfg_reg;    // Configuration register
    
    // Internal signals
    i2c_state_t  state, next_state;
    logic [15:0] clk_cnt;         // Clock divider counter
    logic        clk_en;          // Clock enable pulse
    logic [3:0]  bit_cnt;         // Bit counter (0-8) - increased to 4 bits
    logic [2:0]  byte_cnt;        // Byte counter (0-3)
    logic [7:0]  shift_reg;       // Shift register for data
    logic        scl_int;         // Internal SCL
    logic        sda_int;         // Internal SDA
    logic        rw_bit;          // 0=write, 1=read
    logic        ack_received;    // ACK status
    logic [2:0]  num_bytes;       // Number of bytes to transfer
    logic        addr_sent;       // Address has been sent flag
    logic        byte_complete;   // All 8 bits of current byte sent
    
    // AXI interface signals
    logic        aw_en;
    logic [31:0] axi_awaddr;
    logic [31:0] axi_araddr;
    
    // Calculate actual number of bytes to transfer
    always_comb begin
        if (i2c_nby_reg == 0 || i2c_nby_reg == 1)
            num_bytes = 3'd1;
        else if (i2c_nby_reg == 2)
            num_bytes = 3'd2;
        else if (i2c_nby_reg == 3)
            num_bytes = 3'd3;
        else
            num_bytes = 3'd4;
    end
    
    // Clock divider for I2C timing
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            clk_cnt <= 16'd0;
            clk_en  <= 1'b0;
        end else begin
            if (state == IDLE) begin
                clk_cnt <= 16'd0;
                clk_en  <= 1'b0;
            end else if (clk_cnt >= CLK_DIV) begin
                clk_cnt <= 16'd0;
                clk_en  <= 1'b1;
            end else begin
                clk_cnt <= clk_cnt + 1;
                clk_en  <= 1'b0;
            end
        end
    end
    
    // State machine
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            state <= IDLE;
            rw_bit <= 1'b0;
        end else begin
            state <= next_state;
            
            // Capture R/W bit when starting
            if (state == IDLE && (i2c_cfg_reg[0] || i2c_cfg_reg[2])) begin
                rw_bit <= i2c_cfg_reg[2];  // 1 for read, 0 for write
                $display("I2C: Starting %s transaction for address 0x%h", 
                        i2c_cfg_reg[2] ? "READ" : "WRITE", i2c_adr_reg[6:0]);
            end
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (i2c_cfg_reg[0] || i2c_cfg_reg[2]) begin
                    next_state = START;
                end
            end
            
            START: begin
                if (clk_en) next_state = SEND_ADDR;
            end
            
            SEND_ADDR: begin
                // Transition to RECV_ACK after all 8 bits are sent
                if (clk_en) begin
                    if (bit_cnt == 0 && clk_cnt == 0) begin
                        // All 8 bits sent (bit_cnt wrapped to 0), go to ACK
                        next_state = RECV_ACK;
                    end
                end
            end
            
            RECV_ACK: begin
                if (clk_en) begin
                    if (!ack_received) begin
                        next_state = ERROR;
                    end else if (addr_sent) begin
                        // Data phase ACK
                        if (rw_bit) begin
                            // Read mode - never gets here, handled by SEND_ACK
                        end else begin
                            // Write mode
                            if (byte_cnt >= num_bytes) begin
                                next_state = STOP;
                            end else begin
                                next_state = SEND_DATA;
                            end
                        end
                    end else begin
                        // Address phase ACK
                        if (rw_bit) begin
                            next_state = READ_DATA;
                        end else begin
                            next_state = SEND_DATA;
                        end
                    end
                end
            end
            
            SEND_DATA: begin
                if (clk_en && bit_cnt == 7) next_state = RECV_ACK;
            end
            
            READ_DATA: begin
                if (clk_en && bit_cnt == 8) begin
                    next_state = SEND_ACK;
                end
            end
            
            SEND_ACK: begin
                if (clk_en) begin
                    if (byte_cnt >= num_bytes) begin
                        next_state = STOP;
                    end else begin
                        next_state = READ_DATA;
                    end
                end
            end
            
            STOP: begin
                if (clk_en) next_state = IDLE;
            end
            
            ERROR: begin
                if (clk_en) next_state = STOP;
            end
        endcase
    end
    
    // I2C protocol logic
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            scl_int      <= 1'b1;
            sda_int      <= 1'b1;
            bit_cnt      <= 3'd0;
            byte_cnt     <= 3'd0;
            shift_reg    <= 8'd0;
            ack_received <= 1'b0;
            addr_sent    <= 1'b0;
            i2c_rdr_reg  <= 32'd0;
        end else begin
            // Process I2C logic on every cycle when not IDLE
            if (state != IDLE) begin
                case (state)
                    START: begin
                        if (clk_en) begin
                            $display("I2C State: START");
                            sda_int   <= 1'b0;  // SDA low while SCL high = START
                            shift_reg <= {i2c_adr_reg[6:0], rw_bit};
                            addr_sent <= 1'b0;
                            $display("I2C: Loaded shift_reg = 0x%h (addr=0x%h, rw=%b)", 
                                    {i2c_adr_reg[6:0], rw_bit}, i2c_adr_reg[6:0], rw_bit);
                        end
                    end
                    
                    SEND_ADDR, SEND_DATA: begin
                        // Only generate clock and data for bits 0-7
                        if (bit_cnt < 8) begin
                            // Generate clock
                            if (clk_cnt <= CLK_DIV/2) begin
                                scl_int <= 1'b0;
                            end else begin
                                scl_int <= 1'b1;
                            end
                            
                            // Set SDA at beginning of low period
                            if (clk_cnt == 0) begin
                                sda_int <= shift_reg[7];  // MSB first
                                if (state == SEND_ADDR) begin
                                    $display("I2C: SEND_ADDR[bit=%d] setting SDA=%b from shift_reg[7]=%b (full=0x%h)", 
                                            bit_cnt, shift_reg[7], shift_reg[7], shift_reg);
                                end else begin
                                    $display("I2C: SEND_DATA[bit=%d] setting SDA=%b", bit_cnt, shift_reg[7]);
                                end
                            end else begin
                                // Keep SDA stable during entire bit period
                                sda_int <= shift_reg[7];
                            end
                            
                            // Update bit counter and shift at end of cycle
                            if (clk_cnt == CLK_DIV) begin
                                bit_cnt <= bit_cnt + 1;
                                if (bit_cnt < 7) begin
                                    // Shift for next bit (not on last bit)
                                    shift_reg <= {shift_reg[6:0], 1'b0};
                                    $display("I2C: Sent bit[%d], shifting to 0x%h", 
                                            bit_cnt, {shift_reg[6:0], 1'b0});
                                end else begin
                                    $display("I2C: Sent last bit[7], bit_cnt will be 8");
                                end
                            end
                        end else begin
                            // bit_cnt == 8, just maintain clock until state transition
                            if (clk_cnt <= CLK_DIV/2) begin
                                scl_int <= 1'b0;
                            end else begin
                                scl_int <= 1'b1;
                            end
                            sda_int <= 1'b1;  // Release SDA for ACK
                            $display("I2C: Waiting for ACK state transition (bit_cnt=8)");
                        end
                    end
                    
                    RECV_ACK: begin
                        if (clk_cnt == 0) begin
                            $display("I2C: Entered RECV_ACK state");
                        end
                        
                        // Generate clock
                        if (clk_cnt <= CLK_DIV/2) begin
                            scl_int <= 1'b0;
                            sda_int <= 1'b1;  // Release SDA for slave to drive
                        end else begin
                            scl_int <= 1'b1;
                        end
                        
                        // Reset bit counter for next byte
                        if (clk_cnt == 0) begin
                            bit_cnt <= 4'd0;  // 4-bit counter
                        end
                        
                        // Debug: show SDA value during ACK
                        if (clk_cnt == CLK_DIV/4) begin
                            $display("I2C: ACK slot - SDA released, sda_i=%b", sda_i);
                        end
                        
                        // Sample ACK when SCL is stable high  
                        if (clk_cnt == (3*CLK_DIV/4)) begin
                            ack_received <= ~sda_i;
                            $display("I2C: ACK sampling - sda_i=%b, ACK=%s", 
                                    sda_i, ~sda_i ? "received" : "NOT received");
                        end
                        
                        // Process at end of ACK cycle
                        if (clk_cnt == CLK_DIV) begin
                            if (ack_received) begin
                                if (!addr_sent) begin
                                    addr_sent <= 1'b1;
                                    if (!rw_bit) begin
                                        // Write mode - load first data byte
                                        shift_reg <= i2c_tdr_reg[7:0];
                                        $display("I2C: Loading first data byte: 0x%h", i2c_tdr_reg[7:0]);
                                    end
                                end else if (!rw_bit) begin
                                    // Write mode - data phase
                                    byte_cnt <= byte_cnt + 1;
                                    if (byte_cnt + 1 < num_bytes) begin
                                        case (byte_cnt)
                                            3'd0: shift_reg <= i2c_tdr_reg[15:8];
                                            3'd1: shift_reg <= i2c_tdr_reg[23:16];
                                            3'd2: shift_reg <= i2c_tdr_reg[31:24];
                                        endcase
                                    end
                                end
                            end
                        end
                    end
                    
                    READ_DATA: begin
                        if (clk_cnt <= CLK_DIV/2) begin
                            scl_int <= 1'b0;
                        end else begin
                            scl_int <= 1'b1;
                        end
                        sda_int <= 1'b1;  // Release SDA for slave
                        
                        // Sample data on SCL rising edge
                        if (clk_cnt == CLK_DIV/2 + 1) begin
                            shift_reg <= {shift_reg[6:0], sda_i};
                        end
                        
                        if (clk_cnt == CLK_DIV) begin
                            if (bit_cnt < 8) begin
                                bit_cnt <= bit_cnt + 1;
                                if (bit_cnt == 7) begin
                                    // Store received byte
                                    case (byte_cnt)
                                        3'd0: i2c_rdr_reg[7:0]   <= {shift_reg[6:0], sda_i};
                                        3'd1: i2c_rdr_reg[15:8]  <= {shift_reg[6:0], sda_i};
                                        3'd2: i2c_rdr_reg[23:16] <= {shift_reg[6:0], sda_i};
                                        3'd3: i2c_rdr_reg[31:24] <= {shift_reg[6:0], sda_i};
                                    endcase
                                    $display("I2C: Read byte[%d] = 0x%h", byte_cnt, {shift_reg[6:0], sda_i});
                                end
                            end
                        end
                    end
                    
                    SEND_ACK: begin
                        if (clk_cnt <= CLK_DIV/2) begin
                            scl_int <= 1'b0;
                            // ACK all but last byte
                            sda_int <= (byte_cnt + 1 >= num_bytes) ? 1'b1 : 1'b0;
                        end else begin
                            scl_int <= 1'b1;
                        end
                        
                        if (clk_en) begin
                            byte_cnt <= byte_cnt + 1;
                        end
                    end
                    
                    STOP: begin
                        scl_int <= 1'b1;
                        if (clk_cnt <= CLK_DIV/2) begin
                            sda_int <= 1'b0;
                        end else begin
                            sda_int <= 1'b1;  // STOP condition
                        end
                        
                        if (clk_en) begin
                            $display("I2C: STOP condition");
                        end
                    end
                    
                    ERROR: begin
                        scl_int <= 1'b1;
                        sda_int <= 1'b1;
                        if (clk_en) begin
                            $display("I2C: ERROR state");
                        end
                    end
                    
                    IDLE: begin
                        // This is handled outside the case
                    end
                endcase
            end else begin
                // IDLE state
                scl_int      <= 1'b1;
                sda_int      <= 1'b1;
                bit_cnt      <= 4'd0;  // 4-bit counter
                byte_cnt     <= 3'd0;
                shift_reg    <= 8'd0;
                ack_received <= 1'b0;
                addr_sent    <= 1'b0;
            end
        end
    end
    
    // I2C pin control (open-drain)
    assign scl_o   = 1'b0;
    assign scl_oen = scl_int;
    assign sda_o   = 1'b0;
    assign sda_oen = sda_int;
    
    // Status register management
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            i2c_cfg_reg <= 32'd0;
        end else begin
            // Clear enable bits when starting
            if (state == START && clk_en) begin
                i2c_cfg_reg[0] <= 1'b0;  // Clear TX enable
                i2c_cfg_reg[2] <= 1'b0;  // Clear RX enable
            end
            
            // Set completion bits when done
            if (state == STOP && next_state == IDLE && clk_en) begin
                if (!rw_bit) begin
                    i2c_cfg_reg[1] <= 1'b1;  // TX complete
                    $display("I2C: Write transaction complete");
                end else begin
                    i2c_cfg_reg[3] <= 1'b1;  // RX complete
                    $display("I2C: Read transaction complete");
                end
            end
            
            // Handle software writes
            if (s_axi_awready && s_axi_awvalid && s_axi_wready && s_axi_wvalid) begin
                if (axi_awaddr[7:0] == I2C_CFG) begin
                    // Clear completion bits
                    if (!s_axi_wdata[1]) i2c_cfg_reg[1] <= 1'b0;
                    if (!s_axi_wdata[3]) i2c_cfg_reg[3] <= 1'b0;
                    
                    // Set enable bits only when idle
                    if (state == IDLE) begin
                        if (s_axi_wdata[0] && s_axi_wdata[2]) begin
                            // Both set - prioritize TX
                            i2c_cfg_reg[0] <= 1'b1;
                            i2c_cfg_reg[2] <= 1'b0;
                        end else begin
                            i2c_cfg_reg[0] <= s_axi_wdata[0];
                            i2c_cfg_reg[2] <= s_axi_wdata[2];
                        end
                    end
                end
            end
        end
    end
    
    //----------------------------------------------------------------------
    // AXI4-Lite Interface
    //----------------------------------------------------------------------
    
    // Write address channel
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_awready <= 1'b0;
            aw_en         <= 1'b1;
            axi_awaddr    <= 32'd0;
        end else begin
            if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid && aw_en) begin
                s_axi_awready <= 1'b1;
                axi_awaddr    <= s_axi_awaddr;
                aw_en         <= 1'b0;
            end else if (s_axi_bready && s_axi_bvalid) begin
                s_axi_awready <= 1'b0;
                aw_en         <= 1'b1;
            end else begin
                s_axi_awready <= 1'b0;
            end
        end
    end
    
    // Write data channel
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_wready <= 1'b0;
        end else begin
            if (!s_axi_wready && s_axi_wvalid && s_axi_awvalid && aw_en) begin
                s_axi_wready <= 1'b1;
            end else begin
                s_axi_wready <= 1'b0;
            end
        end
    end
    
    // Write response channel
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_bvalid <= 1'b0;
            s_axi_bresp  <= 2'b00;
        end else begin
            if (s_axi_awready && s_axi_awvalid && !s_axi_bvalid && s_axi_wready && s_axi_wvalid) begin
                s_axi_bvalid <= 1'b1;
                s_axi_bresp  <= 2'b00;
            end else if (s_axi_bvalid && s_axi_bready) begin
                s_axi_bvalid <= 1'b0;
            end
        end
    end
    
    // Register writes
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            i2c_nby_reg <= 32'd1;
            i2c_adr_reg <= 32'd0;
            i2c_tdr_reg <= 32'd0;
        end else begin
            if (s_axi_awready && s_axi_awvalid && s_axi_wready && s_axi_wvalid) begin
                case (axi_awaddr[7:0])
                    I2C_NBY: begin
                        i2c_nby_reg <= s_axi_wdata;
                        $display("I2C: NBY = %d", s_axi_wdata);
                    end
                    I2C_ADR: begin
                        i2c_adr_reg <= s_axi_wdata;
                        $display("I2C: ADR = 0x%h", s_axi_wdata[6:0]);
                    end
                    I2C_TDR: begin
                        i2c_tdr_reg <= s_axi_wdata;
                        $display("I2C: TDR = 0x%h", s_axi_wdata);
                    end
                    I2C_CFG: begin
                        $display("I2C: CFG write = 0x%h", s_axi_wdata);
                    end
                endcase
            end
        end
    end
    
    // Read address channel
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_arready <= 1'b0;
            axi_araddr    <= 32'd0;
        end else begin
            if (!s_axi_arready && s_axi_arvalid) begin
                s_axi_arready <= 1'b1;
                axi_araddr    <= s_axi_araddr;
            end else begin
                s_axi_arready <= 1'b0;
            end
        end
    end
    
    // Read data channel
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_rvalid <= 1'b0;
            s_axi_rdata  <= 32'd0;
            s_axi_rresp  <= 2'b00;
        end else begin
            if (s_axi_arready && s_axi_arvalid && !s_axi_rvalid) begin
                s_axi_rvalid <= 1'b1;
                s_axi_rresp  <= 2'b00;
                
                case (axi_araddr[7:0])
                    I2C_NBY: s_axi_rdata <= i2c_nby_reg;
                    I2C_ADR: s_axi_rdata <= i2c_adr_reg;
                    I2C_RDR: s_axi_rdata <= i2c_rdr_reg;
                    I2C_TDR: s_axi_rdata <= i2c_tdr_reg;
                    I2C_CFG: begin
                        s_axi_rdata <= i2c_cfg_reg;
                        $display("I2C: CFG read = 0x%h", i2c_cfg_reg);
                    end
                    default: s_axi_rdata <= 32'd0;
                endcase
            end else if (s_axi_rvalid && s_axi_rready) begin
                s_axi_rvalid <= 1'b0;
            end
        end
    end
    
endmodule