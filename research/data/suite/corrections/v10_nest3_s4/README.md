# Correction: flow v10, nest3 seed 4 (farm suite13t_s5a_v10_4a_r1 task 10)
The farm task's result line said `status=FAIL draws=3/4`. Its draw 10404 never ran: `FAIL 0/12 cycles 0 ... runts: NO
MONITOR OUTPUT`, and the farm's log records an OOM kill (four GLS runs of this 5449-LUT kernel at once in 16G). The
route was rebuilt here byte for byte (sdf 8651fc19, from that task's sizes_10.vh and seed 4; board_rebuild.sh) and
draw 10404 re-run with the task's own exp.txt and kernels/nest3/vec.hex: **PASS 12/12, 0 pulses under 1 ns, narrowest
4.06 ns, EQUIVALENT**. result.txt / draws.txt here are the farm's with that line corrected; the headline reads them in
place of the farm's. The route is NOT CLEAN (least short, 72 ps over 2 constraints), so nest3 seed 4 is UNFINISHED
either way.
