

all: snitch-app/hello_world.bin cva6-app/bringup

snitch-app/hello_world.bin:
	mkdir -p snitch-app/build
	cd snitch-app/build && cmake .. && make

cva6-app/bringup:
	make -C cva6-app

deploy: snitch-app/hello_world.bin cva6-app/bringup
	scp snitch-app/build/hello_world.bin root@hero-vcu128-02.ee.ethz.ch:/root
	scp cva6-app/bringup root@hero-vcu128-02.ee.ethz.ch:/root
	scp run.sh root@hero-vcu128-02.ee.ethz.ch:/root

clean:
	make -C cva6-app clean
	rm -rf snitch-app/build