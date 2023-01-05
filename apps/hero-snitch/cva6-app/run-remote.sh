#!/bin/sh

# All files are copied to /root/payload

cd /root/payload
dmesg -n 8
# mount -t debugfs none /sys/kernel/debug ||:

rmmod snitch_module.ko ||:
insmod snitch_module.ko

# Debugs
# cat /proc/iomem
# cat /sys/kernel/debug/kernel_page_tables

LD_LIBRARY_PATH=/root/payload ./bringup "$@" | tee -a run.log

rmmod snitch_module.ko

