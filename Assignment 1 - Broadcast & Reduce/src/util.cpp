#include "util.h"

#include <math.h>

MPI_Comm createSquareMesh(MPI_Comm comm) {
    int numProcs = getNumProcs(comm);
    int dims[2] = {(int) sqrt(numProcs), (int) sqrt(numProcs)};
    int periodic[2] = {0, 0};
    
    // create a square mesh topology with all the processes
    MPI_Comm mesh;
    MPI_Cart_create(comm, 2, dims, periodic, 1, &mesh);
    return mesh;
}