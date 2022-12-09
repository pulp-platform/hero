#!/bin/bash

tun_cmd="ssh -L 3334:localhost:3334 bordcomputer -N"
pid_file="ssh_tunnel.pid"

stop () {
    if test -f "$pid_file"; then
        echo "pid file $pid_file exists. Killing.."
        kill $(cat $pid_file)
        rm $pid_file
    else
        echo "pid file not found"
    fi
}

start () {
    echo "starting tunnel ${tun_cmd}"
    nohup ${tun_cmd} > /dev/null 2>&1 & echo $! > ${pid_file}
    echo "started with pid $(cat ${pid_file})"
}

restart () {
    stop ; start
}

case $1 in
    start) start ;;
    stop) stop ;;
    restart) restart ;;
    *)
        echo "Command $1 not found"
    ;;
esac
