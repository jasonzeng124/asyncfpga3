#!/usr/bin/env bash
# Probe C-10l2: route gcd_hw on seeds d 2 3 4 (two at a time) with route.sh.
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
mkdir -p build
(./route.sh d; ./route.sh 3) > build/routeA_f.log 2>&1 &
(./route.sh 2; ./route.sh 4) > build/routeB_f.log 2>&1 &
wait
echo all routes done
