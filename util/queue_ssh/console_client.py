import sys
import time
import os
import random
import subprocess
import socket

queue_file = "queue.txt"
lock_file = "queue.lock"

def sizeof_fmt(num, suffix="B"):
    for unit in ["", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi"]:
        if abs(num) < 1024.0:
            return f"{num:3.1f}{unit}{suffix}"
        num /= 1024.0
    return f"{num:.1f}Yi{suffix}"

def connect_to_server(my_login):
    host = socket.gethostname()
    port = 5002
    client_socket = socket.socket()
    client_socket.connect((host, port))
    print("Connected to server...")
    message = my_login
    client_socket.send(message.encode())
    while True:
        data = client_socket.recv(1024)
        if not data: return
        data = data.decode()
        if(data == "YOUARECONNECTED"):
            break
        print(data)
    
    return client_socket

def send_files(client_socket):
    user_input = ""
    while user_input.lower() != "y":
        if user_input == 'N':
            client_socket.close()
            return None
        files = [f for f in os.listdir('.') if os.path.isfile(f)]
        print("Send : ", end="")
        for f in files:
            print("{} ({}) ".format(f, sizeof_fmt(os.stat(f).st_size)), end="")
        print("\n(y/N)")
        user_input = input()
    return client_socket

def open_terminal(client_socket):
    print("Sending first command...")
    message = "ls"
    while message.lower().strip() != 'exit':
        client_socket.send(message.encode())
        data = client_socket.recv(1024).decode()
        print(data, end="")
        message = input()

    client_socket.close()

def aquire(my_login):
    print("Ready to connect...")
    client_socket = connect_to_server(my_login)
    if client_socket:
        send_files(client_socket)
            
    print("Ready to disconnect...")

def main():
    send_files(0)
    sys.exit(0)
    my_login = os.getlogin() + str(random.randint(10, 11))
    aquire(my_login)
    

if __name__ == '__main__':
    main()