END=$(( $(date +%s) + 12*3600 ))
while [ $(date +%s) -lt $END ]; do
  cd /home/user/b
  find . -path "*/w/m/d0.json" -mmin +20 -delete; find . -path "*/w/m/synth.json" -mmin +20 -delete
  find . -regex ".*/w/[^/]*\.json" -mmin +20 -delete; find . -name "*.frames" -mmin +20 -delete
  find . -name "*dump*.json" -size +10M -mmin +20 -delete; find . -path "*/d1*/net.simx" -mmin +20 -delete
  sleep 600
done
