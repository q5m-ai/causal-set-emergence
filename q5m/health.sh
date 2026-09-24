#!/bin/sh
set -eu

base=http://127.0.0.1:8080
/usr/bin/wget -q -O /dev/null "$base/healthz"
/usr/bin/wget -q -O /dev/null "$base/.q5m-release"
/usr/bin/wget -q -O - "$base/" | /bin/grep -q '<title>Causal Set Emergence'
