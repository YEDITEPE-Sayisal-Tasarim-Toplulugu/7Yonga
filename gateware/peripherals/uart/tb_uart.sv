module uart_tb;
    // Sistem sinyalleri
    reg clk;
    reg rst_n;
    
    // AXI4-Lite arayüzü
    reg [31:0] s_axi_awaddr;
    reg        s_axi_awvalid;
    wire       s_axi_awready;
    reg [31:0] s_axi_wdata;
    reg [3:0]  s_axi_wstrb;
    reg        s_axi_wvalid;
    wire       s_axi_wready;
    wire [1:0] s_axi_bresp;
    wire       s_axi_bvalid;
    reg        s_axi_bready;
    reg [31:0] s_axi_araddr;
    reg        s_axi_arvalid;
    wire       s_axi_arready;
    wire [31:0] s_axi_rdata;
    wire [1:0]  s_axi_rresp;
    wire        s_axi_rvalid;
    reg         s_axi_rready;
    
    // UART pinleri
    wire uart_rx;
    wire uart_tx;
    
    // Test değişkenleri
    reg [31:0] divisor;
    reg [31:0] rx_data;
    reg [31:0] cfg_value;
    integer    i;
    
    // Sabitler
    parameter CLK_PERIOD = 10; // 100 MHz saat
    
    // UART register adresleri
    parameter UART_CPB = 8'h00; // Clock-per-bit register
    parameter UART_STP = 8'h04; // Stop-bit register
    parameter UART_RDR = 8'h08; // Read data register
    parameter UART_TDR = 8'h0C; // Transmit data register
    parameter UART_CFG = 8'h10; // Configuration register
    
    // UART modülü
    uart dut (
        .s_axi_aclk(clk),
        .s_axi_aresetn(rst_n),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wvalid(s_axi_wvalid),
        .s_axi_wready(s_axi_wready),
        .s_axi_bresp(s_axi_bresp),
        .s_axi_bvalid(s_axi_bvalid),
        .s_axi_bready(s_axi_bready),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_rdata(s_axi_rdata),
        .s_axi_rresp(s_axi_rresp),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx)
    );
    
    // TX'i RX'e bağla (loopback testi için)
    assign uart_rx = uart_tx;
    
    // Saat üretimi
    always begin
        clk = 0; #(CLK_PERIOD/2);
        clk = 1; #(CLK_PERIOD/2);
    end
    
    // AXI4-Lite yazma işlemi - daha basit stil
    task axi_write;
        input [31:0] addr;
        input [31:0] data;
        begin
            // AXI sinyallerini ayarla
            s_axi_awaddr = addr;
            s_axi_awvalid = 1'b1;
            s_axi_wdata = data;
            s_axi_wstrb = 4'hF;
            s_axi_wvalid = 1'b1;
            s_axi_bready = 1'b1;
            
            // Adres ve veri kabul edilene kadar bekle
            while (!(s_axi_awready && s_axi_wready)) @(posedge clk);
            
            // Adres ve veri geçerli sinyalleri temizle
            @(posedge clk);
            s_axi_awvalid = 1'b0;
            s_axi_wvalid = 1'b0;
            
            // Yanıt bekle
            while (!s_axi_bvalid) @(posedge clk);
            
            // Yanıt alma işlemi tamamlandı
            @(posedge clk);
            s_axi_bready = 1'b0;
            
            // CPB değerini takip et
            if (addr == UART_CPB) begin
                divisor = data;
                $display("CPB değeri güncellendi: %0d", data);
            end
        end
    endtask
    
    // AXI4-Lite okuma işlemi 
    task axi_read;
        input [31:0] addr;
        output [31:0] data;
        begin
            // Adres ayarla
            s_axi_araddr = addr;
            s_axi_arvalid = 1'b1;
            s_axi_rready = 1'b1;
            
            // Adres kabul edilene kadar bekle
            while (!s_axi_arready) @(posedge clk);
            
            // Adres geçerli sinyalini temizle
            @(posedge clk);
            s_axi_arvalid = 1'b0;
            
            // Veri hazır olana kadar bekle
            while (!s_axi_rvalid) @(posedge clk);
            
            // Veriyi al
            data = s_axi_rdata;
            
            // Veri alma işlemi tamamlandı
            @(posedge clk);
            s_axi_rready = 1'b0;
            
            $display("Adres 0x%h'den okunan değer: 0x%h", addr, data);
        end
    endtask
    
    // Flag bekleyen task - daha basit stil
    // CFG register'da belirli bir bitin 1 olmasını bekleyen task 
    task wait_for_flag;
        input [31:0] bit_index;
        input [31:0] max_cycles;
        begin
            reg [31:0] count;
            reg [31:0] temp_cfg;
            reg flag_found;  // Flag'in bulunup bulunmadığını takip eden bayrak
            
            count = 0;
            flag_found = 0;  // Başlangıçta flag bulunmadı
            
            while (count < max_cycles && !flag_found) begin
                axi_read(UART_CFG, temp_cfg);
                
                if (temp_cfg[bit_index] == 1'b1) begin
                    cfg_value = temp_cfg;  // Çağıran için değeri sakla
                    $display("Flag bit %0d is set! CFG=0x%h", bit_index, cfg_value);
                    flag_found = 1;  // Flag bulundu, döngüden çıkılacak
                end
                else begin
                    count = count + 1;
                    
                    // Okumalar arasında bekle
                    for (i = 0; i < 10; i = i + 1) @(posedge clk);
                end
            end
            
            // Sadece gerçekten timeout olduysa mesaj göster
            if (!flag_found) begin
                $display("CFG register'da bit %0d beklerken timeout!", bit_index);
            end
        end
    endtask
    
    // Test sekansı
    initial begin
        // Sinyalleri başlat
        s_axi_awvalid = 0;
        s_axi_wvalid = 0;
        s_axi_bready = 0;
        s_axi_arvalid = 0;
        s_axi_rready = 0;
        s_axi_wstrb = 4'hF;
        rst_n = 1;
        divisor = 0;
        
        // Reset uygula
        $display("Reset uygulanıyor...");
        #20 rst_n = 0;
        #20 rst_n = 1;
        #20;
        
        $display("9600 baud rate eşdeğeri ile UART testi başlıyor");
        
        // UART yapılandır (simülasyon hızı için küçük bir bölen kullan)
        axi_write(UART_CPB, 50);
        
        // Stop bitlerini 1 olarak ayarla
        axi_write(UART_STP, 0);
        
        // 'A' karakterini gönder (ASCII 65 veya 0x41)
        axi_write(UART_TDR, 8'h41);
        
        // İletimi etkinleştir
        axi_write(UART_CFG, 1); // Bit 0, TX enable
        $display("TX komutu gönderildi, tamamlanması bekleniyor...");
        
        // TX tamamlama flag'ini bekle (bit 2)
        wait_for_flag(2, 10000);
        
        $display("TX tamamlandı flag'i tespit edildi = 0x%h", cfg_value);
        
        // RX tamamlanması için biraz zaman ver
        for (i = 0; i < 100; i = i + 1) @(posedge clk);
        
        // RX veri alındı flag'ini bekle (bit 1)
        wait_for_flag(1, 10000);
        
        $display("RX tamamlandı flag'i tespit edildi = 0x%h", cfg_value);
        
        // RX flag tespitinden sonra tam bir çerçeve süresi bekle
        $display("%0d saat çevrimi bekleniyor (12 * divisor) RDR okumadan önce", divisor * 12);
        for (i = 0; i < divisor * 12; i = i + 1) @(posedge clk);
        
        // Alınan veriyi oku
        axi_read(UART_RDR, rx_data);
        $display("Alınan veri: 0x%h", rx_data[7:0]);
        
        // Durum flag'lerini temizle
        axi_write(UART_CFG, 1); // TX enable, durum flag'lerini temizle
        
        // Alınan verinin doğru olup olmadığını kontrol et
        if (rx_data[7:0] == 8'h41) begin
            $display("Test BAŞARILI: Doğru veri alındı 'A'");
        end
        else begin
            $display("Test BAŞARISIZ: Yanlış veri alındı 0x%h, beklenen 0x41", rx_data[7:0]);
        end
        
        // Sisteme yerleşmesi için biraz zaman ver
        for (i = 0; i < 100; i = i + 1) @(posedge clk);
        
        // Daha yüksek baud rate testi
        $display("\nDaha yüksek baud rate ile UART testi başlıyor");
        
        // Baud rate'i değiştir (simulasyon için 10 kullan)
        axi_write(UART_CPB, 10);
        
        // 'B' karakterini gönder (ASCII 66 veya 0x42)
        axi_write(UART_TDR, 8'h42);
        
        // İletimi etkinleştir (zaten aktif olmalı)
        axi_write(UART_CFG, 1);
        $display("Yüksek baud rate ile ikinci TX komutu gönderildi");
        
        // TX tamamlama flag'ini bekle (bit 2)
        wait_for_flag(2, 10000);
        
        $display("Yüksek baud rate, TX tamamlandı flag'i tespit edildi = 0x%h", cfg_value);
        
        // RX tamamlanması için biraz zaman ver
        for (i = 0; i < 50; i = i + 1) @(posedge clk);
        
        // RX veri alındı flag'ini bekle (bit 1)
        wait_for_flag(1, 10000);
        
        $display("Yüksek baud rate, RX tamamlandı flag'i tespit edildi = 0x%h", cfg_value);
        
        // RX flag tespitinden sonra tam bir çerçeve süresi bekle
        $display("%0d saat çevrimi bekleniyor (12 * divisor) RDR okumadan önce", divisor * 12);
        for (i = 0; i < divisor * 12; i = i + 1) @(posedge clk);
        
        // Alınan veriyi oku
        axi_read(UART_RDR, rx_data);
        $display("Yüksek baud rate ile alınan veri: 0x%h", rx_data[7:0]);
        
        // Durum flag'lerini temizle
        axi_write(UART_CFG, 1); // TX enable, durum flag'lerini temizle
        
        // Alınan verinin doğru olup olmadığını kontrol et
        if (rx_data[7:0] == 8'h42) begin
            $display("Test BAŞARILI: Yüksek baud rate ile doğru veri alındı 'B'");
        end
        else begin
            $display("Test BAŞARISIZ: Yüksek baud rate ile yanlış veri alındı 0x%h, beklenen 0x42", rx_data[7:0]);
        end
        
        // Testleri bitir
        $display("Tüm testler tamamlandı");
        axi_write(UART_CFG, 0); // TX'i kapat
        #1000 $finish;
    end
    
endmodule