# Recompute research/JOURNAL.md means/ratios (origin/claude/research 9a02f6f) from their per-seed numbers.
m = lambda xs: sum(xs) / len(xs)
def show(name, xs, claim):
    print("%-48s n=%d mean=%.3f range=%.1f-%.1f  claim %s" % (name, len(xs), m(xs), min(xs), max(xs), claim))
ipow_base = [103.6, 105.4, 103.0, 107.6, 105.4, 105.7, 106.1, 107.6]   # seeds 1-8, 17 vec
ipow_T6   = [73.8, 77.7, 79.7, 76.0, 78.0, 78.7, 78.8, 76.8]           # seeds 1-8 (training)
ipow_T9_29_32 = [74.6, 77.9, 74.9, 77.1]                               # seeds 29-32
ipow_FF_29_32 = [71.3, 70.3, 74.3, 71.0]
col_pad = [156.3, 160.2, 156.6, 159.6, 158.6, 164.2, 161.9, 157.0]     # seeds 1-8, 16 vec
col_T3  = [98.3, 101.3, 106.1, 107.5, 99.6, 103.4, 102.6, 99.3]
col_FF_1_4 = [92.8, 93.3, 87.4, 90.8]
xs_ph6 = [102.2, 103.0, 102.3, 102.9, 102.0, 100.8, 105.4, 101.5]      # 6 vectors
xs_T3_6 = [61.6, 60.1, 61.6, 61.4, 61.4, 59.1, 59.4, 56.8]             # 6 vectors
xs_T3_14_1_4 = [65.9, 64.4, 65.4, 65.7]                                # 14 vectors
xs_FF_1_4 = [59.6, 59.7, 59.9, 58.7]
gcd_off = [47, 42, 45, 49]                                             # R5 vec6 seeds d,3,4,5
gcd_R5_8 = [47, 42, 45, 49, 50, 48, 49, 48]
show("ipow pads-only seeds1-8", ipow_base, "105.6 (103.0-107.6)")
show("ipow T6 seeds1-8", ipow_T6, "77.4 (73.8-79.7)")
print("  T6 speedup %.3f (claim 1.36); worst/best %.3f (claim 1.29)" % (m(ipow_base)/m(ipow_T6), 103.0/79.7))
show("ipow T9 seeds29-32", ipow_T9_29_32, "76.1")
show("ipow T9+FF seeds29-32", ipow_FF_29_32, "71.7")
print("  FF change %.2f%% (claim -5.8%%); 105.6/71.7 %.3f (claim 1.47, seeds 1-8 vs 29-32)" % (100*(m(ipow_FF_29_32)/m(ipow_T9_29_32)-1), m(ipow_base)/m(ipow_FF_29_32)))
print("  T9 8-seed 76.2: 105.55/76.2 = %.3f (claim 1.39; seeds 1-8 vs 29-36)" % (m(ipow_base)/76.2))
print("  T9+FF 8-seed 72.2: 105.55/72.2 = %.3f (claim 1.46; seeds 1-8 vs 29-36)" % (m(ipow_base)/72.2))
print("  implied T9 seeds 33-36 mean %.2f; implied T9+FF seeds 33-36 mean %.2f (per-seed not published)" % ((76.2*8-sum(ipow_T9_29_32))/4, (72.2*8-sum(ipow_FF_29_32))/4))
show("collatz padded seeds1-8", col_pad, "159.3 (156.3-164.2)")
show("collatz T3 seeds1-8", col_T3, "102.3 (98.3-107.5)")
print("  T3 speedup %.3f (claim 1.56); worst/best %.3f (claim 1.45)" % (m(col_pad)/m(col_T3), 156.3/107.5))
show("collatz T3 seeds1-4", col_T3[:4], "103.3")
show("collatz T3+FF seeds1-4", col_FF_1_4, "91.1")
print("  FF change %.2f%% (claim -11.8%%); 159.3/91.1 = %.3f (claim 1.75; 8-seed vs 4-seed); same-seed padded1-4/FF1-4 = %.3f" % (100*(m(col_FF_1_4)/m(col_T3[:4])-1), m(col_pad)/m(col_FF_1_4), m(col_pad[:4])/m(col_FF_1_4)))
print("  T3+FF 8 seeds 92.1: 159.3/92.1 = %.3f (claim 1.73); implied seeds 5-8 mean %.2f (per-seed not published)" % (m(col_pad)/92.1, (92.1*8-sum(col_FF_1_4))/4))
show("xorshift placeholders 6vec seeds1-8", xs_ph6, "102.5 (100.8-105.4)")
show("xorshift T3 6vec seeds1-8", xs_T3_6, "60.2 (56.8-61.6)")
print("  6-vec speedup %.3f (claim 1.70)" % (m(xs_ph6)/m(xs_T3_6)))
show("xorshift T3 14vec seeds1-4", xs_T3_14_1_4, "65.4")
show("xorshift T3+FF 14vec seeds1-4", xs_FF_1_4, "59.5")
print("  FF change %.2f%% (claim -9.0%%); 102.5(6vec,8seed)/59.5(14vec,4seed)=%.3f (claim 1.72)" % (100*(m(xs_FF_1_4)/m(xs_T3_14_1_4)-1), m(xs_ph6)/m(xs_FF_1_4)))
print("  T3+FF 8 seeds 60.0: 102.5(6vec)/60.0(14vec) = %.3f (claim 1.71); 14-vec/6-vec slope ratio on T3 = %.3f" % (m(xs_ph6)/60.0, 64.3/m(xs_T3_6)))
print("  implied T3+FF seeds 5-8 mean %.2f; implied T3 14vec seeds 5-8 mean %.2f" % ((60.0*8-sum(xs_FF_1_4))/4, (64.3*8-sum(xs_T3_14_1_4))/4))
print("gcd R5 vec6 seeds d,3,4,5 mean %.3f; ON 49.5 -> %+.2f%% (claim +8.2%%)" % (m(gcd_off), 100*(49.5/m(gcd_off)-1)))
print("BOARD-QUEUE #3: ON 8-seed 50.0 vs OFF 4-seed 45.75 = %+.2f%%; vs OFF 8-seed %.3f = %+.2f%%; 'predicts ~0.92x': 4-seed %.3f, 8-seed %.3f" % (100*(50/45.75-1), m(gcd_R5_8), 100*(50/m(gcd_R5_8)-1), 45.75/50, m(gcd_R5_8)/50))
print("README gap column: xorshift %.2f collatz %.2f collatz64 %.2f (claims 3.7/6.5/6.3)" % (47.66/12.73, 91.96/14.05, 112.71/17.84))
