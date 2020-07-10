#!/usr/bin/env bash

if [[ -z $JTAG_VPI_PORT ]]; then
    echo "falling back to default port 9999"
    export JTAG_VPI_PORT=9999
fi

echo "polling until port $JTAG_VPI_PORT opens"

while ! netstat -plnt 2>/dev/null | grep -q "0.0.0.0:$JTAG_VPI_PORT"; do
    sleep 0.1
done

echo "launching openocd"

openocd "$@"
