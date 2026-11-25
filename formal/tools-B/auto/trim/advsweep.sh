# advsweep.sh DIR CLS: kappa sweep of the steer adversary (classes CLS: condition cone slow, request walk fast), corners 0 / 1
d=$1; c=$2; P=$(cat /home/user/b/trim/xs1_step1/j/pairs.txt)
W=$(python3 -c "print(','.join(str(int(l.split()[0],16)) for l in open('/home/user/b/trim/xs1_step1/j/exp.txt') if l.strip() and not l.startswith('//')))")
for cor in 0 1; do for k in 0.05 0.10 0.15 0.20 0.25 0.30 0.40; do
  r=$(KDEN=100 timeout 1200 $d/w/m/simx $d/w/m/net.simx --periodic --maxev 300000000 --kernel xorshift --want $W --pairs $P --corner $cor --kappa $k --classes $c --cdefault M --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 --hostdelay 12000 --w 20 2>&1 | grep -o "RESULT [A-Z_]*" | head -1)
  echo "$d corner $cor kappa $k: $r"; case "$r" in *OK*) ;; *) break;; esac
done; done
