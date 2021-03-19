#!/usr/bin/env bash

this_dir=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")
hero_root_dir="${this_dir}/../.."

hero_config_file=${hero_root_dir}/local.cfg # HERO Config File
hero_petalinux_dir=${hero_root_dir}/petalinux/zcu102 # HERO Petalinux Folder

usage () {
  echo "Usage: $0 [-h | -i <hw_server_ip> | -p <hw_server_port>] -- Reset from XSDB/JTAG"
  echo "Arguments:"
  echo "  -h                   Show this help text"
  echo "  -i <hw_server_ip>    Xilinx HW Server IP   (default: 127.0.0.1)"
  echo "  -p <hw_server_port>  Xilinx HW Server Port (default: 3121)"
  exit 0
}

# HW Server Default Configuration
hw_server_ip=127.0.0.1
hw_server_port=3121

while getopts "hi:p:" option; do
  case "$option" in
    i)  hw_server_ip="$OPTARG" ;;
    p)  hw_server_port="$OPTARG" ;;
    h)  # it's always useful to provide some help
        usage
        exit 0
        ;;
    :)  echo "Error: -$OPTARG requires an argument"
        usage
        exit 1
        ;;
    ?)  echo "Error: unknown option -$OPTARG"
        usage
        exit 1
        ;;
  esac
done

# Print informations
echo "Resetting board at ${hw_server_ip}:${hw_server_port}"

if [ -n "$NO_IIS" ]; then
  PETALINUX_VER=''
else
  if [ -z "$PETALINUX_VER" ]; then
    PETALINUX_VER="vitis-2019.2"
  fi
fi
readonly PETALINUX_VER

# Send Reset Commands through XSDB
cat <<EOF | $PETALINUX_VER xsdb
connect -host ${hw_server_ip} -port ${hw_server_port}

puts -nonewline "Reseting"
targets -set -nocase -filter {name =~ "*PSU*"}
stop
rst -system
after 2000
targets -set -nocase -filter {name =~ "*PMU*"}
stop
rst -system
after 2000
targets -set -nocase -filter {name =~ "*PSU*"}
stop
rst -system
after 2000
mwr 0xFFCA0038 0x1ff
targets -set -nocase -filter {name =~ "*MicroBlaze PMU*"}
dow "${hero_petalinux_dir}/images/linux/pmufw.elf"
after 2000
con
exit
EOF

# That's all folks!!
