# HERO Boot from JTAG+TFTPBOOT+NFS (w/o SDCard)

## Intro
This tutorial shows how to boot the HERO ecosystem on the ZCU102 instance without the usage of SDCard. JTAG will be used to boot FSBL and U-Boot. Linux kernel, which is quite bigger, is loaded through TFTP, while RootFS is exported using NFS. This tutorial will use also static IP for the HERO board.

## 1. Prerequisite
### 1.1. Setup JTAG Boot
Setup the switch on the ZCU102 for JTAG boot (See [https://www.xilinx.com/support/answers/68682.html](https://www.xilinx.com/support/answers/68682.html)).


### 1.2. Setup TFTPBOOT and NFS Server
First, you need to set up your TFT and NFS server. If you have already a TFTP and NFS server installed you can skip this pass.
#### 1.2.1 Install TFTPBOOT and NFS Server packages (Ubuntu)
```
sudo apt update
sudo apt install -y tftpd-hpa nfs-kernel-server
```

#### 1.2.2 Setup NFS Folder
Edit the file `/etc/exports` adding the following line to export an NFS folder (i.e. `/opt/hero/rootfs`) to the HERO board:
```
/opt/hero/rootfs <hero_ip>(rw,nohide,insecure,no_subtree_check,async,no_root_squash)

```
After the file modification, you should execute the command `sudo exportfs -ra` to activate the new configuration.

#### 1.2.3. Setup TFTP Folder
By default, the tftpboot shared folder is located at `/var/lib/tftpboot`. You can select another folder changing in the file `/etc/default/tftpd-hpa` the value of `TFTP_DIRECTORY` (i.e. `TFTP_DIRECTORY="/opt/tftpboot"`). You need also to setup the `--create` to `TFTP_OPTIONS`.

Here an example of `/etc/default/tftpd-hpa`:
```
# /etc/default/tftpd-hpa

TFTP_USERNAME="tftp"
TFTP_DIRECTORY="/opt/tftpboot"
TFTP_ADDRESS=":69"
TFTP_OPTIONS="--secure --create"
```

Then we create the target folder for HERO and we restart the service to update the configuration.
```
sudo mkdir -p /opt/tftpboot
sudo chown root:nogroup /opt/tftpboot
sudo chmod 777 /opt/tftpboot
sudo systemctl restart tftpd-hpa
```
## 2. Setup and Build Custom Configuration of HERO
### 2.1 Setup custom local.cfg
You should modify the `local.cfg` as follow:
```
#
# Buildroot Custom Configurations
#
BR2_HERO_BITSTREAM="<path/to/hero/bistream.bit>"
BR2_HERO_ETH_IP_ADDR="<hero_ip>"
BR2_HERO_ETH_NETMASK="<netmask>"
BR2_HERO_ETH_GATEWAY="<gateway_ip>"
BR2_HERO_ETH_DNS="<dnsserver_ip>"

#
# Petalinux Custom Configurations
#
PT_NFSSERVER_IP="<server_ip>"
PT_ROOTFS_NFS="y"
PT_NFSROOT_DIR="/opt/rootfs"
PT_TFTPBOOT_DIR="/opt/tftpboot"
```
All the `BR2_HERO_ETH_*` values are optional in case you want to use DHCP.

### 2.2 Build HERO Environment
In case it is your first build you can build all you need using the following command:
```
make har-exilzcu102
```

Otherwise, if you had already built all toolchain and the auxiliary environment, you can execute the following command to re-build only the Linux Kernel and the RootFS:
```
make br-har-exilzcu102
```

After the build you need to install the generated files into the NFS and TFTP shared folders:
```
cp output/br-har-exilzcu102/images/Image $PT_TFTPBOOT_DIR
cp output/br-har-exilzcu102/images/system.dtb $PT_TFTPBOOT_DIR
tar -xf output/br-har-exilzcu102/images/rootfs.tar -C $PT_NFSROOT_DIR
```

Note, you can automatically install the generated files executing the following command:
```
util/xsdb/install_tftp_nfs_rootfs.sh
```

### 2.3 Boot U-Boot from JTAG
You can boot FSBL and U-Boot using the following Petalinux command:
```
cd petalinux/zcu102
petalinux-boot --jtag --U-Boot --fpga --bitstream <path/to/hero-bistream.bit> -v --hw_server-url <hwserver_ip>:<hwserver_port>
```
Or you can use the following command:
```
util/xsdb/boot_jtag.sh -i <hwserver_ip> -p <hwserver_port>
```

The boot process takes around 5 minutes. After that, you can access to the U-Boot prompt connecting to the UART port of the board.


### 2.4 Setting U-Boot Bootargs and Boot Linux Kernel (Finally!)
From the U-Boot prompt you need to fix the `bootargs` (due to some problem of petalinux to generate a correct configuration). Here the comand you should execute inside the prompt of U-Boot (adjust with your local configuration):
```
setenv tftpblocksize 512
setenv bootargs console=ttyPS0,115200n8 earlycon clk_ignore_unused ip=<hero_ip>:<server_ip>:<gateway_ip>:<netmask>::eth0:off root=/dev/nfs rootfstype=nfs nfsroot=<server_ip>:/opt/hero/rootfs,tcp,nolock,nfsvers=3 rw
```

Now you are able to boot Linux triggering the following list of commands inside the U-Boot prompt:
```
tftpb 0x200000 Image
tftpb 0x7000000 system.dtb
booti 0x200000 - 0x7000000 ${bootargs}
```
