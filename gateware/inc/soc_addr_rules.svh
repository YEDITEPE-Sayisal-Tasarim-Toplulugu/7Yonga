


`ifndef __SOC_ADDR_RULES_SVH__
`define __SOC_ADDR_RULES_SVH__

package soc_addr_rules_pkg;

typedef logic [31:0] addr_t; 
    
typedef struct packed {
    addr_t       start_addr;
    addr_t       end_addr;
} addr_rule_t;

addr_rule_t ROM_ADDR_RULE = '{
    32'h3000_0000,
    32'h3000_0400
};

addr_rule_t INST_SRAM_ADDR_RULE = '{
    32'h2000_0000,
    32'h2000_2000
};

endpackage

`endif // __SOC_ADDR_RULES_SVH__