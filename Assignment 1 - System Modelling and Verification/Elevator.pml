#define FLOORS 3

mtype { moveUP, moveDOWN, waitUP, waitDOWN };
// 0 - resting, looking for button press above
// 1 - moving up
// 2 - moving down
// 3 - resting, looking for button press below

chan controlToElevator = [0] of {mtype};

// global elevator variables - the floor, the doors and the buttons pressed
int currFloor = 0;
bool isDoorOpen = true;
bool destination[FLOORS];

proctype elevator(chan control) {
    do 
    :: control ? waitUP -> isDoorOpen = true; 
    :: control ? moveUP -> isDoorOpen = false; 
    :: control ? moveDOWN -> isDoorOpen = false; 
    :: control ? waitDOWN -> isDoorOpen = true; 
    od
}

proctype controller(chan output) {
    byte controlState  = waitUP;
    do
    :: controlState == waitUP ->
        atomic { 
            int i = currFloor + 1;
            do  
            // on the top, look for presses below
            :: i == FLOORS -> controlState = waitDOWN -> output ! controlState; break
            // button press above, start moving up
            :: i < FLOORS && destination[i] -> 
                controlState = moveUP -> output ! controlState; break
            :: else -> i++;
            od
        }
    :: controlState == moveUP ->
        atomic { 
            currFloor++;
            if  // check destination & stop, else keep moving
                :: destination[currFloor] -> 
                    controlState = waitUP -> output ! controlState; destination[currFloor] = false
                :: else -> skip
            fi
        }
    :: controlState == moveDOWN ->
        atomic { 
            currFloor--;
            if  // check destination & stop, else keep moving
                :: destination[currFloor] -> 
                    controlState = waitDOWN -> output ! controlState; destination[currFloor] = false
                :: else -> skip
            fi
        }
    :: controlState == waitDOWN ->
        atomic { 
            int i = currFloor - 1;
            do  
            // at the bottom, look for presses above
            :: i < 0 -> controlState = waitUP -> output ! controlState; break
            // button press below, start moving down
            :: i >= 0 && destination[i] -> 
                controlState = moveDOWN -> output ! controlState; break
            :: else -> i--;
            od
        }
    od
}

proctype floorButton(int floor) {
    do  
        :: atomic { floor != currFloor -> destination[floor] = true }
        :: true -> skip
    od
}

init {
    run controller(controlToElevator);
    run elevator(controlToElevator);

    int i = 0;
    do
        :: i < FLOORS -> run floorButton(i); i++ 
    od
}