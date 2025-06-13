`ifndef AXI_LITE_DUMMY_MONITOR__SV
`define AXI_LITE_DUMMY_MONITOR__SV

class axi_lite_dummy_monitor extends uvm_monitor;

  `uvm_component_utils(axi_lite_dummy_monitor)

  virtual axi_lite_if.passive sigs;
  uvm_analysis_port #(axi_lite_rw) ap;
  axi_lite_config cfg;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    axi_lite_agent agent;
    if ($cast(agent, get_parent()) && agent != null) begin
      sigs = agent.vif;
    end
    else begin
      virtual axi_lite_if tmp;
      if (!uvm_config_db#(virtual axi_lite_if)::get(this, "", "vif", tmp)) begin
        `uvm_fatal("AXI/MON/NOVIF", "No virtual interface specified for this monitor instance")
      end
      sigs = tmp;
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    axi_lite_rw tr;

    forever begin
      // WRITE ADDRESS channel handshake
      do @(posedge sigs.pck); while (!(sigs.pck.AWVALID && sigs.pck.AWREADY));
      
      tr = axi_lite_rw::type_id::create("tr", this);
      tr.kind = axi_rw_e::WRITE;
      tr.addr = sigs.pck.AWADDR;

      // WRITE DATA channel handshake
      do @(posedge sigs.pck); while (!(sigs.pck.WVALID && sigs.pck.WREADY));
      if ($isunknown(sigs.pck.WDATA)) begin
        `uvm_error("AXI/MON", "WDATA contains X or Z")
      end
      tr.data = sigs.pck.WDATA;

      // WRITE RESPONSE
      do @(posedge sigs.pck); while (!sigs.pck.BVALID);
      if ($isunknown(sigs.pck.BRESP)) begin
        `uvm_error("AXI/MON", "BRESP is X or Z")
      end

      trans_observed(tr);
      uvm_do_callbacks(axi_lite_dummy_monitor, axi_lite_dummy_monitor_cbs, trans_observed(this, tr));
      ap.write(tr);

      // READ ADDRESS channel
      do @(posedge sigs.pck); while (!(sigs.pck.ARVALID && sigs.pck.ARREADY));

      tr = axi_lite_rw::type_id::create("tr_rd", this);
      tr.kind = axi_rw_e::READ;
      tr.addr = sigs.pck.ARADDR;

      // READ DATA
      do @(posedge sigs.pck); while (!sigs.pck.RVALID);
      if ($isunknown(sigs.pck.RDATA)) begin
        `uvm_error("AXI/MON", "RDATA contains X or Z")
      end
      tr.data = sigs.pck.RDATA;

      trans_observed(tr);
      uvm_do_callbacks(axi_lite_dummy_monitor, axi_lite_dummy_monitor_cbs, trans_observed(this, tr));
      ap.write(tr);
    end
  endtask

  virtual function void trans_observed(axi_lite_rw tr);
    // ...
  endfunction

endclass: axi_lite_dummy_monitor

`endif
