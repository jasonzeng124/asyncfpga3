# fill seed 2 under flow v10 + BDC_MEM_FASTFALL=1 (farm suite13t_s5b_mff_2 task 4): its "FAIL" draw did not run
The task's draw 10201 read `FAIL 0/5 cycles 0 ... MEMORY wrong in batch(es) 0,1,2,3,4 | runts: NO MONITOR OUTPUT`: zero
simulated cycles and no monitor output, so the simulation never started (the "MEMORY wrong" is the judge finding no
arrays read back). The route (shipped it 6, NOT CLEAN, least short; sdf 1b17a79e) was rebuilt here byte for byte with
the task's environment (rerun/fill_s2.spec: board_rebuild.sh, ENV BDC_MEM_FASTFALL=1, fasm ca00867f, no trims) and draw
10201 re-run with the task's exp.txt and memexp.txt (GATE_MEMEXP) and kernels/fill/vec.hex: **PASS 5/5, arrays right,
0 pulses under 1 ns, narrowest 3.40 ns** (rerun/draw_10201.txt, rerun/run.log). Not a wrong answer; the route stays NOT
CLEAN (an opt-in variant's route, not in any headline).
