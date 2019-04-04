## Elevator System

#### Code Structure

* There are processes for the elevator controller, the actual lift and *all* the buttons - the request button on each floor and the destination buttons inside the elevator
* The controller keeps a state machine for the elevator and is responsible for deciding the next move, the elevator process will open/close doors depending on the state
* All button processes are pretty much the same

#### Running the code

To run the code for verification of the following properties

1. *Safety* - the elevator never moves with its doors open

   ```bash
   make run
   ```

2. *Fairness* - The elevator visits every floor infinitely often

   ```bash
   make fair
   ```

3. *Liveness* - Requests to use the elevator are eventually serviced

   ```bash
   make live-request
   ```

4. *Liveness* - Requests to be delivered to a particular floor are eventually serviced

   ```bash
   make live-deliver
   ```

   
