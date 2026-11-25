#!/bin/bash
# run slices, at most 2 at once
printf "%s\n" "$@" | xargs -P 2 -I{} /tmp/claude-0/slice/runslice3.sh {}
echo done > /tmp/claude-0/slice/QUEUE3_$(echo "$@" | tr ' ' _).done
