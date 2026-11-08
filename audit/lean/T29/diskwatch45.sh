#!/usr/bin/env bash
# stop build45 if free disk < 250 MB (the per-module guard cannot act inside one lake call)
while ! grep -q B45DONE /home/user/asyncfpga3/audit/lean/T29/build45.log 2>/dev/null; do
  a=$(df --output=avail -m /root | tail -1)
  if [ "$a" -lt 250 ]; then pkill -f build45.sh; pkill -f "lake build FormalWit"; sleep 2; pkill -f "bin/lean /root/wt-f14/formal/lean/FormalWit"; echo "WATCHDOG STOP $a MB $(date -u +%FT%TZ)" >> /root/build45.log; cp /root/build45.log /home/user/asyncfpga3/audit/lean/T29/build45.log; echo B45DONE >> /home/user/asyncfpga3/audit/lean/T29/build45.log; exit; fi
  sleep 20; done
