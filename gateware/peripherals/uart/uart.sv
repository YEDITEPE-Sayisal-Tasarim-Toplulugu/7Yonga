module uart (
    // Clock and reset signals
    input  logic        s_axi_aclk,
    input  logic        s_axi_aresetn,
    
    // AXI4-Lite Slave Arayüzü
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
    
    // UART pins
    input  logic        uart_rx,
    output logic        uart_tx
);
    // Register adresleri 
    localparam UART_CPB = 8'h00; // Clock-per-bit register
    localparam UART_STP = 8'h04; // Stop-bit register
    localparam UART_RDR = 8'h08; // Read data register
    localparam UART_TDR = 8'h0C; // Transmit data register
    localparam UART_CFG = 8'h10; // Configuration register
    
    // Register tanımları
    logic [31:0] uart_cpb_reg;  // Clock-per-bit register
    logic [31:0] uart_stp_reg;  // Stop-bit register
    logic [31:0] uart_rdr_reg;  // Read data register
    logic [31:0] uart_tdr_reg;  // Transmit data register
    logic [31:0] uart_cfg_reg;  // Configuration register
    logic tx_data_updated;      // TDR güncellendiğinde set edilir
    logic rx_data_updated;      // RDR güncellendiğinde set edilir

    // TX ve RX durum makineleri
    localparam IDLE  = 2'b00;
    localparam START = 2'b01;
    localparam DATA  = 2'b10;
    localparam STOP  = 2'b11;
    
    // TX sinyalleri
    logic [1:0] tx_state;
    logic tx_active;
    logic tx_done;
    logic [31:0] tx_counter;
    logic [2:0] tx_bit_idx;
    
    // RX sinyalleri
    logic [1:0] rx_state;
    logic rx_active;
    logic rx_done;
    logic [31:0] rx_counter;
    logic [2:0] rx_bit_idx;
    logic [7:0] rx_data;
    
    // Stop bits hesaplama
    logic [31:0] stop_cycles;
    
    // AXI handshake yardımcı değişkenleri
    logic        aw_en;
    logic [31:0] axi_awaddr;
    logic [31:0] axi_araddr;
    
    //----------------------------------------------------------------------
    // AXI4-Lite Arayüzü - Yazma Kanalı
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_awready <= 1'b0;
            s_axi_wready  <= 1'b0;
            s_axi_bvalid  <= 1'b0;
            s_axi_bresp   <= 2'b00;
            aw_en         <= 1'b1;
            axi_awaddr    <= 32'd0;
            
            // Register sıfırlama
            uart_cpb_reg <= 32'd0;
            uart_stp_reg <= 32'd0;
            uart_tdr_reg <= 32'd0;
            uart_cfg_reg <= 32'd0;
            tx_data_updated <= 1'b0;
            rx_data_updated <= 1'b0;
        end else begin
            // Varsayılan değer
            tx_data_updated <= 1'b0;
            
            // AWREADY (adres kabulü)
            if (!s_axi_awready && s_axi_awvalid && s_axi_wvalid && aw_en) begin
                s_axi_awready <= 1'b1;
                axi_awaddr    <= s_axi_awaddr;
                aw_en         <= 1'b0;
            end else if (s_axi_bready && s_axi_bvalid) begin
                s_axi_awready <= 1'b0;
                aw_en         <= 1'b1;
            end
            
            // WREADY (veri kabulü)
            if (!s_axi_wready && s_axi_wvalid && s_axi_awvalid && aw_en) begin
                s_axi_wready <= 1'b1;
            end else begin
                s_axi_wready <= 1'b0;
            end
            
            // Write response
            if (s_axi_awready && s_axi_awvalid && !s_axi_bvalid && s_axi_wready && s_axi_wvalid) begin
                s_axi_bvalid <= 1'b1;
                s_axi_bresp  <= 2'b00; // OKAY
            end else if (s_axi_bvalid && s_axi_bready) begin
                s_axi_bvalid <= 1'b0;
            end
            
            // Donanım olayları (register yazma işlemleri daha öncelikli)
            if (rx_done) begin
                uart_rdr_reg <= {24'b0, rx_data}; // RX veri register güncelleme
                rx_data_updated <= 1'b1; // RDR güncellendiğini işaretle
                $display("RDR updated with 0x%h, will set RX flag next cycle", rx_data);
            end
            
            // RX flag'i, veri güncellendikten bir çevrim sonra ayarla
            if (rx_data_updated) begin
                uart_cfg_reg[1] <= 1'b1; // Data received flag ayarla
                rx_data_updated <= 1'b0; // Güncelleme sinyalini sıfırla
                $display("Setting RX flag for data 0x%h", uart_rdr_reg[7:0]);
            end
            
            if (tx_done) begin
                uart_cfg_reg[2] <= 1'b1; // TX completed flag ayarla
                $display("Setting TX completed flag");
            end
            
            // Register yazma işlemi - sadece adres ve veri hazır olduğunda
            if (s_axi_awready && s_axi_awvalid && s_axi_wready && s_axi_wvalid) begin
                case (axi_awaddr[7:0])
                    UART_CPB: uart_cpb_reg <= s_axi_wdata;
                    UART_STP: uart_stp_reg <= s_axi_wdata;
                    UART_TDR: begin
                        uart_tdr_reg <= s_axi_wdata;
                        tx_data_updated <= 1'b1; // TDR güncellendiğini işaretle
                        $display("TDR updated with 0x%h", s_axi_wdata[7:0]);
                    end
                    UART_CFG: begin
                        // TX enable bitini her zaman güncelle
                        uart_cfg_reg[0] <= s_axi_wdata[0];
                        
                        // Yazılım flag'leri sadece 0 yazmakla temizleyebilir
                        if (s_axi_wdata[1] == 1'b0) begin 
                            uart_cfg_reg[1] <= 1'b0; // RX flag temizle
                            $display("Clearing RX flag");
                        end
                        if (s_axi_wdata[2] == 1'b0) begin
                            uart_cfg_reg[2] <= 1'b0; // TX flag temizle
                            $display("Clearing TX flag");
                        end
                    end
                    default: ; // Hiçbir şey yapma
                endcase
            end
        end
    end

    //----------------------------------------------------------------------
    // AXI4-Lite Arayüzü - Okuma Kanalı
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            s_axi_arready <= 1'b0;
            s_axi_rvalid  <= 1'b0;
            s_axi_rresp   <= 2'b00;
            axi_araddr    <= 32'd0;
        end else begin
            // ARREADY (okuma adresi kabulü)
            if (!s_axi_arready && s_axi_arvalid) begin
                s_axi_arready <= 1'b1;
                axi_araddr    <= s_axi_araddr;
            end else begin
                s_axi_arready <= 1'b0;
            end
            
            // RVALID (okuma verisi hazır)
            if (s_axi_arready && s_axi_arvalid && !s_axi_rvalid) begin
                s_axi_rvalid <= 1'b1;
                s_axi_rresp  <= 2'b00; // OKAY
                
                case (axi_araddr[7:0])
                    UART_CPB: s_axi_rdata <= uart_cpb_reg;
                    UART_STP: s_axi_rdata <= uart_stp_reg;
                    UART_RDR: s_axi_rdata <= uart_rdr_reg;
                    UART_TDR: s_axi_rdata <= uart_tdr_reg;
                    UART_CFG: s_axi_rdata <= uart_cfg_reg;
                    default:  s_axi_rdata <= 32'd0;
                endcase
                
                // $display("Reading address 0x%h, value = 0x%h", axi_araddr, s_axi_rdata);
            end else if (s_axi_rvalid && s_axi_rready) begin
                s_axi_rvalid <= 1'b0;
            end
        end
    end
    
    //----------------------------------------------------------------------
    // Stop bit hesaplama
    //----------------------------------------------------------------------
    always_comb begin
        if (uart_stp_reg[1:0] == 2'b00)
            stop_cycles = uart_cpb_reg; 
        else if (uart_stp_reg[1:0] == 2'b01)
            stop_cycles = uart_cpb_reg + (uart_cpb_reg >> 1); 
        else
            stop_cycles = uart_cpb_reg << 1;
    end
    
    //----------------------------------------------------------------------
    // UART verici (transmitter)
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            tx_state <= IDLE;
            tx_active <= 1'b0;
            tx_done <= 1'b0;
            tx_counter <= 32'd0;
            tx_bit_idx <= 3'd0;
            uart_tx <= 1'b1;
        end else begin
            tx_done <= 1'b0;
            
            case (tx_state)
                IDLE: begin
                    uart_tx <= 1'b1;
                    tx_counter <= 32'd0;
                    tx_bit_idx <= 3'd0;
                    
                    if (uart_cfg_reg[0] && ~uart_cfg_reg[2] && ~tx_done && (tx_data_updated || !tx_active)) begin
                        tx_active <= 1'b1;
                        tx_state <= START;
                        $display("TX: Starting transmission of 0x%h", uart_tdr_reg[7:0]);
                    end
                end
                
                START: begin
                    uart_tx <= 1'b0; // Start bit (low)
                    
                    if (tx_counter < uart_cpb_reg - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        tx_state <= DATA;
                        $display("TX: Start bit completed");
                    end
                end
                
                DATA: begin
                    uart_tx <= uart_tdr_reg[tx_bit_idx]; // Send data bit
                    
                    if (tx_counter < uart_cpb_reg - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        
                        if (tx_bit_idx < 7) begin
                            tx_bit_idx <= tx_bit_idx + 1;
                            $display("TX: Sent bit %0d = %0d", tx_bit_idx, uart_tdr_reg[tx_bit_idx]);
                        end else begin
                            tx_bit_idx <= 3'd0;
                            tx_state <= STOP;
                            $display("TX: All data bits sent");
                        end
                    end
                end
                
                STOP: begin
                    uart_tx <= 1'b1; // Stop bit (high)
                    
                    if (tx_counter < stop_cycles - 1) begin
                        tx_counter <= tx_counter + 1;
                    end else begin
                        tx_counter <= 32'd0;
                        tx_state <= IDLE;
                        tx_active <= 1'b0;
                        tx_done <= 1'b1; // Set TX completed flag
                        $display("TX: Stop bit completed, transmission done");
                    end
                end
                
                default: tx_state <= IDLE;
            endcase
        end
    end
    
    //----------------------------------------------------------------------
    // UART alıcı (receiver)
    //----------------------------------------------------------------------
    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (!s_axi_aresetn) begin
            rx_state <= IDLE;
            rx_active <= 1'b0;
            rx_done <= 1'b0;
            rx_counter <= 32'd0;
            rx_bit_idx <= 3'd0;
            rx_data <= 8'd0;
        end else begin
            rx_done <= 1'b0;
            
            case (rx_state)
                IDLE: begin
                    rx_active <= 1'b0;
                    rx_counter <= 32'd0;
                    rx_bit_idx <= 3'd0;
                    
                    if (uart_rx == 1'b0 && !rx_active & 
                        ~(rx_done | rx_data_updated | uart_cfg_reg[1])
                    ) begin
                        rx_state <= START;
                        rx_active <= 1'b1;
                        $display("RX: Start bit detected");
                    end
                end
                
                START: begin
                    if (rx_counter < (uart_cpb_reg >> 1) - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        if (uart_rx == 1'b0) begin
                            rx_state <= DATA;
                            $display("RX: Valid start bit confirmed");
                        end else begin
                            rx_state <= IDLE; 
                            rx_active <= 1'b0;
                            $display("RX: False start detected");
                        end
                    end
                end
                
                DATA: begin
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_data[rx_bit_idx] <= uart_rx; 
                        $display("RX: Sampled bit %0d = %0d", rx_bit_idx, uart_rx);
                        
                        if (rx_bit_idx < 7) begin
                            rx_bit_idx <= rx_bit_idx + 1;
                        end else begin
                            rx_bit_idx <= 3'd0;
                            rx_state <= STOP;
                            $display("RX: All data bits received: 0x%h", {rx_data[6:0], uart_rx});
                        end
                    end
                end
                
                STOP: begin
                    if (rx_counter < uart_cpb_reg - 1) begin
                        rx_counter <= rx_counter + 1;
                    end else begin
                        rx_counter <= 32'd0;
                        rx_state <= IDLE;
                        rx_active <= 1'b0;
                        
                        if (uart_rx == 1'b1) begin
                            rx_done <= 1'b1; 
                            $display("RX: Stop bit valid, reception complete for byte 0x%h", rx_data);
                        end else begin
                    
                            $display("RX: Framing error, invalid stop bit");
                        end
                    end
                end
                
                default: rx_state <= IDLE;
            endcase
        end
    end
    
endmodule
