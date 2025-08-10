


`ifndef __SOC_ADDR_RULES_SVH__
`define __SOC_ADDR_RULES_SVH__

package soc_addr_rules_pkg;

typedef logic [3:0] id_t; 
typedef logic [31:0] addr_t; 

typedef struct packed {
    addr_t      start_addr;
    addr_t      end_addr;
} addr_rule_t;

localparam addr_rule_t ROM_ADDR_RULE = '{
    32'h0000_0000,
    32'h0000_0400
};

localparam addr_rule_t INST_SRAM_ADDR_RULE = '{
    32'h1000_0000,
    32'h1000_2000
};

///////////////////////////////////////////////////////////////////////////////////////////////////////
// SOC'de bulunan DATA interface modülü;
// çekirdekten gelen istek data memory'e gidecekse <DATA_SRAM_ADDR_RULE> adresi aralığını kullanır
// çekirdekten gelen istek diğer modüllere gidecekse <AXI_MASTER_ADDR_RULE> adresi aralığını kullanır
localparam addr_rule_t DATA_SRAM_ADDR_RULE = '{
    32'h2000_0000,
    32'h2000_2000
};

localparam addr_rule_t AXI_MASTER_ADDR_RULE = '{
    32'h0000_0000,
    32'h1F00_0000
};
///////////////////////////////////////////////////////////////////////////////////////////////////////

localparam addr_rule_t PERIPHERALS_TOP_ADDR_RULE = '{
    32'h0001_0000,
    32'h00FF_0000
};

///////////////////////////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Çevre Birimleri Adres Kuralları
localparam addr_rule_t AXIL_UART_ADDR_RULE = '{
    32'h0001_0000,
    32'h0001_0030
};

endpackage

`endif // __SOC_ADDR_RULES_SVH__
