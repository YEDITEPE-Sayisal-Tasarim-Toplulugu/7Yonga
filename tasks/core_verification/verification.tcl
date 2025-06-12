# 7Yonga
# Yeditepe Üniversitesi, Sayısal Tasarım Topluluğu
# 06.2025

set CURRENT_DIR [pwd]
set CORE_DIR [pwd]/../../gateware/core
# set TESTPROGRAM_DIR ${CURRENT_DIR}/testprogram/firstapp
set TESTPROGRAM_DIR ${CURRENT_DIR}/testprogram/coremark/OUT
set OUT_DIR ${CURRENT_DIR}/OUT

create_project my_sim_proj ${OUT_DIR}/my_sim_proj -part xc7a35tcpg236-1 -force

add_files ${TESTPROGRAM_DIR}/program.mem

# Dosya listesini oku ve ekle
set file_list_path ${OUT_DIR}/files.f

# Dosyayı aç ve oku
set fh [open $file_list_path r]
set content [read $fh]
close $fh

# Satırları al ve boş olanları at
set lines [split $content "\n"]

set valid_files {}

foreach line $lines {
    set trimmed_line [string trim $line]
    # Boş satır ve yorumları at
    if {$trimmed_line eq "" || [string index $trimmed_line 0] eq "#"} {
        continue
    }
    lappend valid_files $trimmed_line
}

set include_paths [list "${CURRENT_DIR}/testsuit" \
             "${CURRENT_DIR}/testsuit/inc" \
             "${CORE_DIR}/cv32e40p/rtl/include/" \
             "${CORE_DIR}/cv32e40p/vendor/pulp_platform_fpnew/src/" \
             "${CORE_DIR}/cv32e40p/vendor/pulp_platform_common_cells/src/" \
             "${CORE_DIR}/cv32e40p/vendor/pulp_platform_common_cells/include/" \
             "${CORE_DIR}/cv32e40p/vendor/pulp_platform_common_cells/include/common_cells"]

# Simulation fileset'e ekle (her bir alt simulation filesetine ayrı ayrı eklenmeli)
set_property include_dirs $include_paths [get_filesets sim_1]

set_property verilog_define "VERILATOR" [get_filesets sim_1]

# Dosyaları ekle
add_files {*}$valid_files

# Testbench dosyasını ayrıca ekle (isteğe bağlı)
add_files -fileset sim_1 ./testsuit/tb_suit.sv

set_property top tb_suit [get_filesets sim_1]

create_run sim_1 -flow {Vivado Synthesis 2017}

reset_run sim_1
launch_runs sim_1 -jobs 4
launch_simulation
run 5s