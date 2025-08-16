`ifndef AXI_LITE_RW_SV
`define AXI_LITE_RW_SV

class axi_rw extends uvm_sequence_item;

  typedef enum {READ, WRITE} kind_e;

  rand bit [31:0] addr;
  rand logic [31:0] data;
  rand kind_e kind;

  `uvm_object_utils_begin(axi_rw)
    `uvm_field_int(addr, UVM_ALL_ON | UVM_NOPACK)
    `uvm_field_int(data, UVM_ALL_ON | UVM_NOPACK)
    `uvm_field_enum(kind_e, kind, UVM_ALL_ON | UVM_NOPACK)
  `uvm_object_utils_end

  function new(string name = "axi_rw");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("kind=%s addr=0x%08h data=0x%08h", 
                     (kind == READ) ? "READ" : "WRITE", addr, data);
  endfunction

endclass: axi_rw

`endif 