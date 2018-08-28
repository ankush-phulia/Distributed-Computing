SPIN = spin
MAX_DEPTH = 100000
RUN_FLAGS = -run -v -DNOREDUCE -DNFAIR=3 -m$(MAX_DEPTH)
SAFETY_FLAGS = -a -f
FAIRNESS_FLAGS = -l -f
REPLAY_FLAGS = -t -p
SRC_FILE = Elevator.pml

run :
	$(SPIN) $(RUN_FLAGS) $(SRC_FILE)

clean:
	rm -rf pan* dot* *.trail *.tmp
