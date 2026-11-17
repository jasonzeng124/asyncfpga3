#!/usr/bin/env bash
# T138b: full SLOW_MAX rerun (T139's hangdog stopped the first one at 10/13 vectors), then the fit again.
until [ -f /root/t139.done ]; do sleep 60; done
rm -f /root/t138.done; sed -i '/^DONE$/d' /root/t138.log; echo "T138b SLOW_MAX rerun $(date -u)" >> /root/t138.log
bash /home/user/asyncfpga3/audit/t138/resume.sh
