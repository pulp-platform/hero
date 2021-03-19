#!/usr/bin/env bash

this_dir=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")
hero_root_dir="${this_dir}/../.."

hero_config_file=${hero_root_dir}/local.cfg # HERO Config File
hero_petalinux_dir=${hero_root_dir}/petalinux/zcu102 # HERO Petalinux Folder

usage () {
  echo "Usage: $0 [-h | -i <hw_server_ip> | -p <hw_server_port>] -- Boot u-boot from XSDB/JTAG"
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

if [ -n "$NO_IIS" ]; then
  PETALINUX_VER=''
else
  if [ -z "$PETALINUX_VER" ]; then
    PETALINUX_VER="vitis-2019.2"
  fi
fi
readonly PETALINUX_VER

# Boot HERO from JTAG
eval hero_bitstream=$(grep BR2_HERO_BITSTREAM ${hero_config_file} | sed 's/.*=//' | tr -d '"')
if [ -z "${hero_bitstream}" ]; then
    echo "ERROR: please set BR2_HERO_BITSTREAM in local.cfg file"
else
    cd ${hero_petalinux_dir}
    echo "Booting Petalinux project: ${hero_petalinux_dir}"
    echo "HW Server: ${hw_server_ip}:${hw_server_port} Bitstream: ${hero_bitstream}"
    $PETALINUX_VER petalinux-boot --jtag -v --hw_server-url tcp:${hw_server_ip}:${hw_server_port} --u-boot --fpga --bitstream ${hero_bitstream}
fi

# That's all folks!!
