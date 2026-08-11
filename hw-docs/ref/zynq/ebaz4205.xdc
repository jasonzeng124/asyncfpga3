# EBAZ4205 pin constraints for boards/xc7/zynq/*_ps_top.v harnesses:
# everything rides M_AXI_GP0 (no package pins), only the two PL LEDs are
# physical. Copied verbatim from async-hls-v2's zynq/ebaz4205.xdc (the
# pin assignments that silicon-validated knapsack/gcd on this exact board).
# Pin sites per community pinout (xjtuecho/EBAZ4205).
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
