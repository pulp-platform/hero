#!/bin/sh

echo 1 > /proc/sys/kernel/printk
mount -t debugfs none /sys/kernel/debug ||:

insmod /usr/lib/snitch.ko

# Debugs
cat /proc/iomem
cat /sys/kernel/debug/kernel_page_tables

./bringup hello_world.bin | tee -a run.log

rmmod snitch.ko

