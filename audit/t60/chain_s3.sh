#!/usr/bin/env bash
# T60 row 7: spot check of a second bench route (NEXTPNR_SEED=3): p8mo and x0.5 base, same worst case, 83.3 MHz
cd /home/user/asyncfpga3/audit/t60
bash build_s3.sh > build_p8s3.log 2>&1
bash build_base_s3.sh > build_bases3.log 2>&1
bash run_worst_s3.sh p8s3_worst
bash run_base_s3.sh s50s3_worst83
for t in p8s3_worst s50s3_worst83; do cp /root/t60/$t.log .; python3 /root/t40/oracle.py check /root/t40/xorshift17.hex /root/t60/$t.log 2 > ${t}_oracle.txt; done
rm -rf /root/t60/work_*; echo CHAINDONE > chain_s3.done
