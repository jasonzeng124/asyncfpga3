cd /home/user/b/trim
export RSTRIM=/home/user/rs RS=/home/user/rsx2
bash /home/user/asyncfpga3/formal/tools-B/auto/trim/kshrink.sh lfsrfind1_untrimmed lfsrfind 1 /home/user/b/ff/trim_lfsrfind_s1/trim_record.txt ks_lfsrfind1 "1 2 3 5" > ks_lfsrfind1.txt 2>&1
bash /home/user/asyncfpga3/formal/tools-B/auto/trim/kshrink.sh countloop2_untrimmed countloop 2 /home/user/b/ff/trim_countloop_s2/trim_record.txt ks_countloop2 "1 2 3 5" > ks_countloop2.txt 2>&1
