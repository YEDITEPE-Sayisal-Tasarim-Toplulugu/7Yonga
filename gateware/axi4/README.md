## Vivado için include hatası:
"axi/" yolu ile belirtilen include satırlarından alınan hata için çözüm include pathlerini vivadoya eklemektir. Bunun için TCL Console yerine aşağıdaki satırları yazınız.

```tcl
# Include yolunu tanımla (örneğin axi klasörü ./src/ içinde yer alıyor)
set include_paths [list "./7Yonga/gateware/axi4/axi/include" "./7Yonga/gateware/pulp_common_cell/common_cells/include" "./7Yonga/gateware/inc"]

# Simulation fileset'e ekle (her bir alt simulation filesetine ayrı ayrı eklenmeli)
set_property include_dirs $include_paths [get_filesets sim_1]

# Synthesis fileset'e de ekle
set_property include_dirs $include_paths [get_filesets sources_1]
```


## Verilator ve Xsim(Vivado) - System Verilog Desteklenmeyen Eklentiler.
Bazı system verilog kodları Verilator ve Xsim(Vivado) ile desteklenmiyor, (örnek iff). 

### Örnek Hata:
```text
ERROR: [XSIM 43-3980] File "./7Yonga/gateware/axi4/axi/src/axi_to_detailed_mem.sv" Line 594 : The SystemVerilog feature "Default Disable iff declaration" is not supported yet for simulation.
```

Bu yüzden Vivado'da aşağıdaki komutun TCL Console yazılması gerekir.


```tcl
set_property verilog_define "VERILATOR" [get_filesets sim_1]
```