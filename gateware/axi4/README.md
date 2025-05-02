## Vivado için include hatası:
"axi/" yolu ile belirtilen include satırlarından alınan hata için çözüm include pathlerini vivadoya eklemektir. Bunun için TCL Console yerine aşağıdaki satırları yazınız.

```tcl
# Include yolunu tanımla (örneğin axi klasörü ./src/ içinde yer alıyor)
set include_paths [list "./7Yonga/gateware/axi4/axi/include" "./7Yonga/gateware/pulp_common_cell/common_cells/include"]

# Simulation fileset'e ekle
set_property include_dirs $include_paths [get_filesets sim_1]

# Synthesis fileset'e de ekle
set_property include_dirs $include_paths [get_filesets sources_1]
```