#!/usr/bin/env bash

echo "polling until port opens"

while ! netstat -plnt 2>/dev/null | grep -q 0.0.0.0:9999; do
    sleep 0.1
done

echo "launching openocd"

openocd "$@"
