import paramiko
import socket
import subprocess
import _thread
import queue
import time

class HeroClient():
    def __init__(self, hero_user, client_socket):
        self.hero_user = hero_user
        self.client_socket = client_socket

class CheckableQueue(queue.Queue): # or OrderedSetQueue
    def __contains__(self, item):
        with self.mutex:
            return item in self.queue
    def peek(self):
        with self.mutex:
            return self.queue[0]
    def __str__(self):
        res = ""
        with self.mutex:
            for item in self.queue:
                res += " <- " + str(item)
        return res

def exec_command(ssh, command):
    print(command)
    ssh_stdin, ssh_stdout, ssh_stderr = ssh.exec_command(command)
    out = "".join(ssh_stdout.readlines())
    err = "".join(ssh_stderr.readlines())
    return out+err


hero_ip = "hero-vcu128-02.ee.ethz.ch"
hero_user = "cykoenig"
command = "ls"
key_file = "/home/cykoenig/.ssh/id_rsa"

queue_file = "queue.txt"
lock_file = "queue.lock"

host_socket = socket.gethostname()
port_socket = 5002  # initiate port no above 1024
                                                                                                                                                                         
def on_new_hero(hero, hero_queue):
    print("Starting "+hero)
    while True:
        print("{} ready to wait".format(hero))
        hero_client = hero_queue.get(block=True)
        client_socket = hero_client.client_socket
        client_socket.send("You have been attributed {}".format(hero).encode())
        
        time.sleep(100)
        
        client_socket.close()

def on_new_client(clientsocket, addr, login_queue, hero_queues):
    hero_login = clientsocket.recv(1024).decode()
    print("Receiving "+hero_login)
    if hero_login in login_queue:
        print("User {} is already in the queue".format(hero_login))
        clientsocket.send("User {} is already in the queue".format(hero_login).encode())
        clientsocket.close()
        return

    login_queue.put(hero_login)
    
    clientsocket.send("User {} added to the queue.\n".format(hero_login).encode())
    clientsocket.send("Queue : {}".format(str(login_queue)).encode())
    
    while True:
        if login_queue.peek() != hero_login:
            time.sleep(50)
            clientsocket.send("Queue : {}".format(str(login_queue)).encode())
            continue
    # Start CS
        for hero, hero_queue in hero_queues.items():
            success = False
            try:
                hero_queue.put(HeroClient(hero_login, clientsocket), block=True, timeout=1)
                print("{} added to queue {}, exiting".format(hero_login, hero))
                success = True
                break
            except queue.Full:
                pass
        if success:
            break
    # End CS
    login_queue.get()

def main():
    s = socket.socket()
    
    print("Server started!")
    s.bind((host_socket, port_socket))
    s.listen(5)
    
    # Client queue
    login_queue = CheckableQueue()
    # Hero queues
    hero_queues = {"hero1" : CheckableQueue(1)}
    for hero, hero_queue in hero_queues.items():
        _thread.start_new_thread(on_new_hero,(hero, hero_queue))

    while True:
       clientsocket, addr = s.accept()
       print("Got connection from", addr)
       _thread.start_new_thread(on_new_client,(clientsocket,addr, login_queue, hero_queues))
       
    s.close()

#def start_session(hero_login, clientsocket):
#    ssh_root = paramiko.SSHClient()
#    ssh_root.set_missing_host_key_policy(paramiko.AutoAddPolicy())
#  
#    ssh_root.connect(hero_ip, username="root", key_filename=key_file)
#    print("Connected to", hero_ip, "as root.")
#
#    ret = exec_command(ssh_root, "/root/add_hero_user.sh " + hero_user)
#    print("Set up user ", hero_user + ".")
#    ssh_root.close()
#    conn.send(ret.encode())
#    subprocess.run("ssh -N -L 5001:127.0.0.1:22 "+hero_user+"@hero-vcu128-02.ee.ethz.ch -i "+key_file, shell=True, check=True)
#    conn.send("You may now connect to 5001:127.0.0.1:22".encode())
#    while True:
#        command = conn.recv(1024).decode()
#        sleep(1)

if __name__ == "__main__":
    main()