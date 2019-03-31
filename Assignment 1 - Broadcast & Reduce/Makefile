CC = mpic++
CXXFLAGS = -std=c++11 -I include/

BUILD_TYPE = test
ifeq ($(BUILD_TYPE), debug)
	CXXFLAGS += -g
else
	CXXFLAGS += -O3
endif

all:
	$(CC) src/* $(CXXFLAGS) -o main

clean : 
	rm -f main