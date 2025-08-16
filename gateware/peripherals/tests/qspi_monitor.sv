`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 16.08.2025 22:50:07
// Design Name: 
// Module Name: qspi_monitor
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

// qspi_if.sv
interface qspi_if (
    input  logic                       clk,      // sim/SoC ana saat (senkron reset vb. için)
    input  logic                       rst_n,
    input  logic                       peripheral_qspi_sclk_o,
    input  logic                       peripheral_qspi_cs_no,
    input  logic [3:0]                 peripheral_qspi_data_o,
    input  logic [3:0]                 peripheral_qspi_data_i,
    input  logic [3:0]                 peripheral_qspi_data_oen  // 0: DUT sürer (TX), 1: giriş (RX)
);
    // Monitörün rahat erişmesi için yeniden adlandırma
    logic        sclk;
    logic        cs_n;
    logic [3:0]  dq_o;     // DUT -> dış dünya (flash)
    logic [3:0]  dq_i;     // dış dünya (flash) -> DUT
    logic [3:0]  dq_oen;   // 0: çıkış aktif, 1: giriş

    assign sclk   = peripheral_qspi_sclk_o;
    assign cs_n   = peripheral_qspi_cs_no;
    assign dq_o   = peripheral_qspi_data_o;
    assign dq_i   = peripheral_qspi_data_i;
    assign dq_oen = peripheral_qspi_data_oen;

    // Modport (opsiyonel)
    modport MON (input sclk, cs_n, dq_o, dq_i, dq_oen, clk, rst_n);
endinterface


// qspi_monitor.sv
module qspi_monitor #(
    // SPI mode seçimi (default: Mode 0 -> CPOL=0, CPHA=0)
    parameter bit CPOL = 1'b0,
    parameter bit CPHA = 1'b0,
    // Log ayrıntı seviyesi
    parameter int LOG_LEVEL = 1    // 0: kısa, 1: özet+byte dump, 2: her kenar
) (
    qspi_if.MON bus
);

    // İç yardımcı türler
    typedef enum int {DIR_TX=0, DIR_RX=1} dir_e;

    // Aktif örnekleme kenarı: SPI moduna göre
    function automatic bit is_sample_edge (input bit sclk_prev, input bit sclk_now);
        bit rising  = (sclk_prev == 0) && (sclk_now == 1);
        bit falling = (sclk_prev == 1) && (sclk_now == 0);
        // CPOL/CPHA tablosu: sample kenarı = (CPHA==0 ? 1. kenar : 2. kenar)
        // Mode 0: sample posedge, Mode 1: sample negedge, Mode 2: sample negedge, Mode 3: sample posedge
        if (CPOL==0 && CPHA==0) return rising;
        if (CPOL==0 && CPHA==1) return falling;
        if (CPOL==1 && CPHA==0) return falling;
        /* CPOL=1, CPHA=1 */    return rising;
    endfunction

    // OEN'den hat genişliği (1/2/4) ve yön (TX/RX) kestirimi
    function automatic void decode_bus_mode(
        input  logic [3:0] oen,
        output int         width,     // 1,2,4
        output dir_e       dir
    );
        // Heuristik:
        //  - 4'b0000: DUT tüm hatları sürüyor  => width=4, DIR_TX
        //  - 4'b1111: DUT tüm hatları input    => width=4, DIR_RX
        //  - 4'b0001 veya 4'b1110: genelde 1-bit
        //  - 4'b0011/1100: genelde 2-bit (dual)
        //  - Diğer karma değerleri de yaklaşık ele al
        unique case (oen)
            4'b0000: begin width=4; dir=DIR_TX; end
            4'b1111: begin width=4; dir=DIR_RX; end
            4'b0001: begin width=1; dir=DIR_TX; end // IO0 MOSI
            4'b1110: begin width=1; dir=DIR_RX; end // IO1/2/3 kullanılmıyor kabulü
            4'b0011: begin width=2; dir=DIR_TX; end // IO1..0
            4'b1100: begin width=2; dir=DIR_RX; end
            default: begin
                // Karma durum: '0' sayısı sürülen hat sayısıdır
                int zeros = (oen[0]==0)+(oen[1]==0)+(oen[2]==0)+(oen[3]==0);
                int ones  = 4-zeros;
                if (zeros > ones) begin width = (zeros>=3)?4:((zeros==2)?2:1); dir=DIR_TX; end
                else               begin width = (ones >=3)?4:((ones==2)?2:1); dir=DIR_RX; end
            end
        endcase
    endfunction

    // Numune alma: mevcut moda göre bit/nibble çıkar
    function automatic logic [3:0] sample_dq(
        input dir_e dir, input int width,
        input logic [3:0] dq_o, input logic [3:0] dq_i
    );
        logic [3:0] v = (dir==DIR_TX) ? dq_o : dq_i;
        case (width)
            1: sample_dq = {3'b000, v[0]};          // IO0
            2: sample_dq = {2'b00,  v[1:0]};        // IO1:IO0 (MSB:IO1 varsayımı)
            default: sample_dq = v[3:0];            // Quad: IO3..IO0
        endcase
    endfunction

    // Bir çerçeve boyunca toplanan veriyi byte byte yazdır
    task automatic dump_bytes(
        input dir_e dir, input bit  data_bits [$]
    );
        int nbits;
        int nfull;
        int rem  ;
        string d = (dir==DIR_TX) ? "TX" : "RX";
        if (data_bits.size() == 0) return;
        
        nbits = data_bits.size();
        nfull = nbits/8;
        rem   = nbits%8;

        if (LOG_LEVEL>=1)
            $display("[%0t] QSPI %s %0d bit toplandı (=%0d byte + %0d bit)", $time, d, nbits, nfull, rem);

        if (nfull==0 && LOG_LEVEL==0) return;

        // MSB-first kabulü: her örnekte soldan sağa concat ettik
        for (int i=0; i<nfull; i++) begin
            byte b;
            for (int k=0; k<8; k++) b = {b[6:0], data_bits[i*8 + k]};
            $write("%s[%0d]=0x%02x  ", d, i, b);
            if (((i+1)%16)==0) $write("\n");
        end
        if ((nfull%16)!=0) $write("\n");

        if (rem>0 && LOG_LEVEL>=1) begin
            // Kalan bitleri de göster
            string s=""; 
            for (int k=0; k<rem; k++) s = {s, data_bits[nfull*8+k] ? "1":"0"};
            $display("[%0t] QSPI %s kalan %0d bit: %s (MSB->LSB)", $time, d, rem, s);
        end
    endtask

    // Ana izleme süreci
    initial begin : monitor_main
        bit prev_sclk;
        bit cs_active;

        bit  tx_bits[$]; // MSB-first akış (her sample kenarında width kadar bit eklenir)
        bit  rx_bits[$];

        dir_e cur_dir;
        int   cur_width;

        cs_active = 0;
        
        // Resetten çıkışı bekle
        wait (bus.rst_n === 1'b1);
        prev_sclk = bus.sclk;

        forever begin
            // CS düşüşünü yakala -> yeni transfer
            @(negedge bus.cs_n or posedge bus.cs_n or posedge bus.sclk);
            // CS düşüşü: yeni çerçeve başlangıcı
            if (!bus.cs_n && !cs_active) begin
                cs_active = 1;
                tx_bits.delete();
                rx_bits.delete();
                decode_bus_mode(bus.dq_oen, cur_width, cur_dir);
                if (LOG_LEVEL>=1)
                    $display("[%0t] QSPI CS# ASSERT (start). Mode=%0d%0d width=%0d dir=%s",
                             $time, CPOL, CPHA, cur_width, (cur_dir==DIR_TX)?"TX":"RX");
            end

            // CS aktifken SCLK’ı izle ve örnekle
            if (cs_active) begin
                bit sclk_now;
                logic [3:0] nib;
                
                // SCLK değişimini yakala
                @(posedge bus.sclk or negedge bus.sclk or posedge bus.cs_n);
                if (bus.cs_n) begin
                    // Çerçeve bitti
                    cs_active = 0;
                    if (LOG_LEVEL>=1)
                        $display("[%0t] QSPI CS# DEASSERT (end).", $time);

                    // Dump
                    dump_bytes(DIR_TX, tx_bits);
                    dump_bytes(DIR_RX, rx_bits);
                    continue;
                end

                // Örnekleme kenarı mı?
                sclk_now = bus.sclk;
                if (is_sample_edge(prev_sclk, sclk_now)) begin
                    // Her kenarda anlık oen’e bakıp faz geçişlerini yakalayalım
                    decode_bus_mode(bus.dq_oen, cur_width, cur_dir);
                    nib = sample_dq(cur_dir, cur_width, bus.dq_o, bus.dq_i);

                    if (LOG_LEVEL>=2)
                        $display("[%0t] QSPI sample: width=%0d dir=%s data=0x%1h (IO3..IO0)",
                                 $time, cur_width, (cur_dir==DIR_TX)?"TX":"RX", nib);

                    // Bitleri MSB-first sırada biriktir
                    if (cur_width==4) begin
                        // IO3 MSB, IO0 LSB varsayımı
                        if (cur_dir==DIR_TX) begin
                            tx_bits.push_back(nib[3]); tx_bits.push_back(nib[2]);
                            tx_bits.push_back(nib[1]); tx_bits.push_back(nib[0]);
                        end else begin
                            rx_bits.push_back(nib[3]); rx_bits.push_back(nib[2]);
                            rx_bits.push_back(nib[1]); rx_bits.push_back(nib[0]);
                        end
                    end else if (cur_width==2) begin
                        if (cur_dir==DIR_TX) begin
                            tx_bits.push_back(nib[1]); tx_bits.push_back(nib[0]);
                        end else begin
                            rx_bits.push_back(nib[1]); rx_bits.push_back(nib[0]);
                        end
                    end else begin // width==1
                        if (cur_dir==DIR_TX) tx_bits.push_back(nib[0]);
                        else                 rx_bits.push_back(nib[0]);
                    end
                end
                prev_sclk = sclk_now;
            end
        end
    end
endmodule
