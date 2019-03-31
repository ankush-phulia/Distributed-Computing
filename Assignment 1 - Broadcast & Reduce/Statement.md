#### COV 880 - Assignment 1

Write an MPI program to implement the broadcast and reduce collectives on a 2D mesh using `MPI_Send` and `MPI_Receive` (Do not use other routines for communicating data). Combine these to implement the `allreduce` collective. 

Assume that the total number of nodes, n, is a perfect square (let n = sqrt(n) * sqrt(n)). In order to simulate a 2D mesh, a node i should only communicate with the following nodes -

1. node i - 1, if (i-1) div sqrt(n) == i div sqrt(n)
2. node i + 1, if (i+1) div sqrt(n) == i div sqrt(n)
3. node i - sqrt(n), if i >= sqrt(n) 
4. node i + sqrt(n), if i < n - sqrt(n) 


Your algorithm should minimise the maximum data passed on any link of the 2D mesh.