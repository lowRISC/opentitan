database -shm -open waves.shm -default
probe -create -shm tb -depth all -all -mem
#probe -create -shm tb -depth all
run
exit
