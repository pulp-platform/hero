
count=16
i=0

while [ ${i} -le ${count} ]
do
  ssh root@hero-zcu102-06.ee.ethz.ch "cd /home/root/mmaxim &&\
  export LD_LIBRARY_PATH=/home/root/mmaxim/lib:/home/root/mmaxim/lib_orig &&\
  ./dma-perf"
done

