#define numFloors 3

mtype { moveUP, moveDOWN, waitUP, waitDOWN };
// 0 - resting, looking for button press above
// 1 - moving up
// 2 - moving down
// 3 - resting, looking for button press below

chan controlToElevator = [0] of {mtype};

// elevator variables - the floor, the doors and the buttons pressed
int currElevatorFloor = 0;
bool isDoorOpen = true;
bool destinations[numFloors];

// the "request elevator" button on each floor
bool requests[numFloors];


proctype elevator(chan control) {
    byte state;
    do 
    ::  control ? state;
        if
            :: state == waitUP -> isDoorOpen = true; 
            :: state == moveUP -> isDoorOpen = false; 
            :: state == waitDOWN -> isDoorOpen = true;
            :: state == moveDOWN -> isDoorOpen = false; 
        fi
    // door is closed when elevator moves
    :: assert ((state != moveUP || !isDoorOpen) || (state != moveDOWN || !isDoorOpen))
    od
}

proctype controller(chan output) {
    byte controlState  = waitUP;
    do
    :: controlState == waitUP ->
        progressWUP:
        atomic { 
            int i = currElevatorFloor + 1;
            do  
            // on the top, look for presses below
            :: i == numFloors -> controlState = waitDOWN; break
            // button press above, start moving up
            :: i < numFloors && (destinations[i] || requests[i])-> 
                controlState = moveUP -> output ! controlState; break
            :: else -> i++;
            od
        }
    :: controlState == moveUP ->
        atomic { 
            currElevatorFloor++;
            if  // check destinations & stop, else keep moving
                :: (destinations[currElevatorFloor] || requests[currElevatorFloor]) -> 
                    controlState = waitUP -> output ! controlState; 
                    destinations[currElevatorFloor] = false; requests[currElevatorFloor] = false;
                :: else -> skip
            fi
        }
    :: controlState == moveDOWN ->
        atomic { 
            currElevatorFloor--;
            if  // check destinations & stop, else keep moving
                :: (destinations[currElevatorFloor] || requests[currElevatorFloor])-> 
                    controlState = waitDOWN -> output ! controlState;
                    destinations[currElevatorFloor] = false; requests[currElevatorFloor] = false;
                :: else -> skip
            fi
        }
    :: controlState == waitDOWN ->
        progressWDOWN:
        atomic { 
            int i = currElevatorFloor - 1;
            do  
            // at the bottom, look for presses above
            :: i < 0 -> controlState = waitUP; break
            // button press below, start moving down
            :: i >= 0 && (destinations[i] || requests[i]) -> 
                controlState = moveDOWN -> output ! controlState; break
            :: else -> i--;
            od
        }
    od
}

proctype destinationButton(int floor) {
    do  
    :: floor != currElevatorFloor -> destinations[floor] = true
    od
}

proctype floorButton(int floor) {
    do  
    :: floor != currElevatorFloor -> requests[floor] = true
    od
}

init {
    // start the controller and the elevator
    run controller(controlToElevator);
    run elevator(controlToElevator);

    // start the button processes for each floor
    int i = 0;
    do
    :: i < numFloors -> run destinationButton(i); run floorButton(i); i++ 
    od
}