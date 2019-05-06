# temporary script to display hostname to distinguish between host and chroot
hostname -F /etc/hostname
host=$(hostname)
export PS1="($host) \\$ "
