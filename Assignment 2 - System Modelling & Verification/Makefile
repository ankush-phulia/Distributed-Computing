SPIN = spin
MAX_DEPTH = 100000
RUN_FLAGS = -run -v -DNOREDUCE -DNFAIR=3 -m$(MAX_DEPTH)
SAFETY_FLAGS = -a -f
FAIRNESS_FLAGS = -l -f
REPLAY_FLAGS = -t -p
SRC = Elevator.pml

run :
	$(SPIN) $(RUN_FLAGS) -noclaim $(SRC)

safe :
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -noclaim $(SRC)

fair :
	$(SPIN) $(RUN_FLAGS) $(FAIRNESS_FLAGS) -noclaim $(SRC)

live-request :
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -NliveRequest $(SRC)

live-deliver : 
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -NliveDestination $(SRC) 

replay :
	$(SPIN) $(REPLAY_FLAGS) $(SRC)

clean:
	rm -rf pan* dot* *.trail *.tmp
