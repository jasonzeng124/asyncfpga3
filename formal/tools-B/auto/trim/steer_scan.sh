# steer settle gaps (ucmpi0.uz -> ucond_br*) at 4 corners for each judged trim dir given
cd /home/user/b/trim; P=$(cat xs1_step1/j/pairs.txt)
for r in "$@"; do for b in 0.20,0.31,1.0 0.20,0.31,0.20 0.31,0.20,1.0 0.20,0.20,1.0; do
  g=$(timeout 1200 nice python3 /home/user/asyncfpga3/formal/tools-B/auto/xsteer.py xs1_step1/j/exp.txt $r/w/m 'ucmpi0\.uz' --kernel xorshift --pairs $P --bands $b 2>&1 | grep -v '^SLICE' | awk '/RESULT/{res=$0} /smallest/{split($0,a,"gaps \\["); split(a[2],b,","); if(min==""||b[1]+0<min){min=b[1]+0; s=$1}; split($0,c," requests, "); split(c[2],d," "); ru+=d[1]} END{print substr(res,index(res,"RESULT"),12), "min", min, "at", s, "live-runts", ru+0}')
  echo "$r bands $b: $g"
done; done
