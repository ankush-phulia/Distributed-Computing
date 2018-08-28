#define FLOORS 3

mtype = { mUP, mDOWN, uWAIT, dWAIT };
int currFloor = 0;
bool destination[FLOORS];

proctype elevator() {
    byte state = uWAIT;
    // 0 - resting, looking for button press above
    // 1 - moving up
    // 2 - moving down
    // 3 - resting, looking for button press below

    do
    :: state == uWAIT ->
        atomic { 
            int i = currFloor + 1;
            do 
            // on the top, look for presses below
            :: i == FLOORS -> state = dWAIT; break
            // button press above, start moving up
            :: i < FLOORS && destination[i] -> state = mUP; break
            :: else -> i++;
            od
        }
    :: state == mUP ->
        atomic { 
            currFloor++;
            if  // check destination & stop, else keep moving
                :: destination[currFloor] -> state = uWAIT; destination[currFloor] = false
                :: else -> skip
            fi
        }
    :: state == mDOWN ->
        atomic { 
            currFloor--;
            if  // check destination & stop, else keep moving
                :: destination[currFloor] -> state = dWAIT; destination[currFloor] = false
                :: else -> skip
            fi
        }
    :: state == dWAIT ->
        atomic { 
            int i = currFloor - 1;
            do 
            // at the bottom, look for presses above
            :: i < 0 -> state = uWAIT; break
            // button press below, start moving down
            :: i >= 0 && destination[i] -> state = mDOWN; break
            :: else -> i--;
            od
        }
    od
}

proctype floorButton(int floor) {
    do  :: atomic { floor != currFloor -> destination[floor] = true }
        :: true -> skip
    od
}

init {
    run elevator();
    int i = 0;
    do ::
        i < FLOORS -> run floorButton(i); 
        i++ 
    od
}