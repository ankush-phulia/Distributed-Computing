#### Assignment 1

Write an MPI program to implement the broadcast and reduce collectives on a 2D mesh using `MPI_Send` and `MPI_Receive` (Do not use other routines for communicating data). Combine these to implement the `allreduce` collective. 

Assume that the total number of nodes, n, is a perfect square (let n = m * m). In order to simulate a 2D mesh, a node i should only communicate with the following nodes -

1. node i - 1, if (i - 1) / m == i / m
2. node i + 1, if (i + 1) / m == i / m
3. node i - m, if i >= m
4. node i + m, if i < n - m


The algorithm should minimise the maximum data passed on any link of the 2D mesh.

(Optional) Pipeline data across links