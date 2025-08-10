// M. Furkan UZUN

`define ZEXP(_bits, _data)              {{(_bits){1'b0}}, _data}
`define SEXP(_bits, _length, _data)     {{(_bits){_data[_length-1]}}, _data}
`define BCPY(_bits, _bit)               {(_bits){_bit}}

`define ASSERT(_cond, _msg) \
    if (!(_cond)) begin \
        $display("COMPARE-ERROR: time: [%0t ps] (%s) failed! %0d", $time, `__FILE__, `__LINE__); \
        $display("  Condition : %s", `"(_cond)`"); \
        $display("  Message   : %s", _msg); \
        $finish; \
    end