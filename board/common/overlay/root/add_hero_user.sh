#!/bin/ash
if [ -z "$1" ]
then
    echo "Usage : ./add_hero_user.sh username"
    exit 1
fi

hero_user=$1
mkdir -p "/home/$1/.ssh"
cp /root/.ssh/authorized_keys /home/$1/.ssh/authorized_keys
chmod 755 /home
chmod 755 /home/$1
chmod 700 /home/$1/.ssh
chmod 600 /home/$1/.ssh/authorized_keys
printf "password_sup3r_secret\npassword_sup3r_secret" | adduser $hero_user
