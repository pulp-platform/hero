

all: snitch-app/hello_world.bin cva6-app/bringup

snitch-app/hello_world.bin:
	mkdir -p snitch-app/build
	cd snitch-app/build && cmake .. && make

cva6-app/bringup:
	make -C cva6-app

deploy: snitch-app/hello_world.bin cva6-app/bringup
	mkdir -p deploy_standalone
	cp run.sh cva6-app/bringup cva6-app/file_to_offload.txt snitch-app/build/hello_world.bin deploy_standalone
	rsync -r deploy_standalone root@hero-vcu128-02.ee.ethz.ch:/root/
clean:
	make -C cva6-app clean
	rm -rf snitch-app/build deploy_standalone