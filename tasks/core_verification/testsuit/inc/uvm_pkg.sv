package uvm_pkg;
endpackage

/*
`define  uvm_error(ID, MSG)  ;
`define  uvm_info(ID, MSG, VERBOSITY)  ;
*/

`define uvm_error(ID, MSG)  \
    $display("ERROR [%s]: %s", ID, MSG); \
    $fatal;

`define uvm_info(ID, MSG, VERBOSITY)  \
    if (VERBOSITY >= 0) begin \
        $display("INFO [%s]: %s", ID, MSG); \
    end

`define uvm_fatal(INFO_TAG, MSG)  \
    $display("FATAL [%s]: %s", INFO_TAG, MSG); \
    $fatal;