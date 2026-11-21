#!/usr/bin/env bash
# results.sh -- compile research/data/benchcap/results.txt from the runs (corner_audit outputs under runs/ca)
C=/tmp/bot/sa/gcdclean/runs/ca; L=/tmp/bot/sa/loopfast/runs; S=/tmp/bot/sa/gcdclean/scratch; R=/tmp/bot/sa/gcdclean/repo
row() { grep -E "^  (A|j) .*$2 ([0-9]+ links (joined|from)|joined)" "$1/report.txt" | sort -u | head -2 | cut -c1-260 | sed 's/^/      /'; }
echo "# benchcap results (subagent gcdclean).  corner_audit as auto_size.sh's rule() runs it (CA_SIZERULE=1 CA_JOINAWARE=1"
echo "# BD_SKEW_AND_JOIN=1 BD_SKEW_STEER_SELF=1 CA_FAST=1 PYTHONHASHSEED=1 --band C --inst-rx chains:0.20), scratch ca_run.sh."
echo "# 'orig' = the tool at c7ca40e39 (git worktree), 'new' = this change with CA_BENCHCAP unset, 'bc' = CA_BENCHCAP=1."
echo "# loopfast = subagent loopfast's rule outputs on the same routes (the shipped rule; PYTHONHASHSEED not pinned there)."
echo
echo "== 1. unset = byte-identical (orig vs new, every output file)"
for k in xs14 co14 ga15 isp15; do for c in 0.20 0.31; do
  [ -d $C/${k}_orig_$c ] && [ -d $C/${k}_new_$c ] || continue
  echo "  $k $c: $(python3 $S/cmp_ca.py $C/${k}_orig_$c $C/${k}_new_$c | tail -1)"; done; done
echo
echo "== 2. isprime seed 1 it 5 (su_isprime_1_5, nextpnr 6e5d224472232d5d, NEXTPNR_SEED 1)"
for c in 0.20 0.31; do
  B=$C/isp15_orig_$c; [ -d $B ] || B=$L/ca/su_isprime_1_5/rule_$c
  echo "  corner $c  baseline $(basename $(dirname $B))/$(basename $B)"
  echo "    shipped rule:  $(grep -h '^proposal' $B.txt 2>/dev/null || grep -h '^proposal' $L/auto/su_isprime_1/ca_5_$c.txt)"; row $B umux13
  echo "    CA_BENCHCAP=1: $(grep -h '^proposal' $C/isp15_bc_$c.txt)"; row $C/isp15_bc_$c umux13
  echo "    UMUX13 line: $(grep UMUX13 $B/lines.tsv | cut -f2,3,8) -> $(grep UMUX13 $C/isp15_bc_$c/lines.tsv | cut -f2,3,8)"
  echo "    verify: $(sed -n 2p $B/verify.txt) -> $(sed -n 2p $C/isp15_bc_$c/verify.txt)"
done
echo
echo "== 3. gcd seed 1 it 0 (gcdchk_0, nextpnr 6e5d224472232d5d, NEXTPNR_SEED 1)"
for c in 0.20 0.31; do
  B=$C/gcd0_orig_$c; [ -f $B/negative_sized.tsv ] || B=$L/ca/gcdchk_0/rule_$c
  echo "  corner $c  baseline $B"
  row $B umux21; row $C/gcd0_bc_$c umux21
  echo "    proposal: $(grep -h '^proposal' $C/gcd0_bc_$c.txt)  [CA_BENCHCAP=1]"
  echo "    UMUX21 line: $(grep UMUX21 $B/lines.tsv | cut -f2,3,8) -> $(grep UMUX21 $C/gcd0_bc_$c/lines.tsv | cut -f2,3,8)"
  echo "    verify: $(sed -n 2p $B/verify.txt) -> $(sed -n 2p $C/gcd0_bc_$c/verify.txt)"
done
echo
echo "== 4. other kernels, corner 0.20: CA_BENCHCAP=1 vs orig (what moves)"
for k in xs14 co14 ga15; do
  echo "  -- $k: $(grep -h '^proposal' $C/${k}_orig_0.20.txt)  ->  $(grep -h '^proposal' $C/${k}_bc_0.20.txt)"
  python3 $S/cmp_ca.py $C/${k}_orig_0.20 $C/${k}_bc_0.20 -v | grep -E '^  sizes|RESULT' | sed 's/^/  /'
  grep -E '^  (A|j|a) ' $C/${k}_orig_0.20/report.txt | grep -E 'joined: not applied' | sort -u | cut -c1-200 | sed 's/^/    orig: /'
  grep '\[bench:' $C/${k}_bc_0.20/report.txt | sort -u | cut -c1-330 | sed 's/^/    bc:   /'
  diff <(sed -n '/^NEGATIVE/,/^$/p' $C/${k}_orig_0.20/report.txt | grep -E '^  [AEFHIKLBCj] ') <(sed -n '/^NEGATIVE/,/^$/p' $C/${k}_bc_0.20/report.txt | grep -E '^  [AEFHIKLBCj] ') | grep '^[<>]' | cut -c1-200 | sed 's/^/    neg /'
done
