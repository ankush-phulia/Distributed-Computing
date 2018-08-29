SPIN = spin
MAX_DEPTH = 1000000
RUN_FLAGS = -run -v -DNOREDUCE -DNFAIR=3 -m$(MAX_DEPTH)
SAFETY_FLAGS = -a -f
FAIRNESS_FLAGS = -l -f
REPLAY_FLAGS = -t -p
SRC = Elevator.pml

run :
	$(SPIN) $(RUN_FLAGS) $(SRC)

safe :
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) $(SRC)

fair :
	$(SPIN) $(RUN_FLAGS) $(FAIRNESS_FLAGS) $(SRC)

# live :


# live-deliver : 


replay :
	$(SPIN) $(REPLAY_FLAGS) $(SRC)

clean:
	rm -rf pan* dot* *.trail *.tmp
