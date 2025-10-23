vlog -work work -vopt -sv -stats=none +cover=bcesft C:/Users/dachu/Desktop/uvm_multislave_multimaster/apb_uvm_verification/top.svh
vsim -coverage -assertdebug -voptargs=+acc work.apb_tb_top -l log.txt
add wave -position insertpoint sim:/apb_tb_top/intf/*
run -all
coverage report -cvg -details
coverage report -codeAll
coverage report -assert -details
coverage save -onexit apb_coverage_with_assert.ucdb


