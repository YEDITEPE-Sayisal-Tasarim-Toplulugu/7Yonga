



`ifndef AXI4_AGENT__SV
`define AXI4_AGENT__SV

typedef class axi_agent;

class axi_lite_agent extends uvm_agent;

    axi_lite_sequencer = sqr; // sequencer define edilmeli
    axi_lite_master = drv; // master(driver) define edilmeli
    axi_lite_dummy_monitor = mon;

    axi_lite_if       vif;

    uvm_active_passive_enum is_active = UVM_ACTIVE;


    function new (string name, uvm_componenet parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        
        mon = axi_lite_dummy_monitor::type_id::create("mon",this);

        if (is_active == UVM_ACTIVE) begin
            sqr = axi_lite_sequencer::type_id::create("sqr", this);
            drv = axi_lite_driver::type_id::create("drv", this);
        end

        if(!uvm_config_db#(axi_lite_if)::get(this, "", "vif",vif)) begin
            `uvm_fatal("AXI_LITE,NOVIF", "No virtual interface specified for this agent instance")
        end

    endfunction: build_phase

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        if (is_active == UVM_ACTIVE) begin
            drv.seq_item_port.connect(sqr.seq_item_export);
        end
    endfunction

endclass: axi_lite_agent

`endif