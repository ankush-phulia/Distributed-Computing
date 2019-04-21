#ifndef UTIL_H
#define UTIL_H

#include <mpi.h>

enum direction { LEFT = -1, RIGHT = 1 }; 

inline int getGlobalRank() {
    int globalRank;
    MPI_Comm_rank(MPI_COMM_WORLD, &globalRank);
    return globalRank;
}

inline int getLocalRank(MPI_Comm comm) {
    int localRank;
    MPI_Comm_rank(comm, &localRank);
    return localRank;
}

inline int getNumProcs(MPI_Comm comm) {
    int numProcs;
    MPI_Comm_size(comm, &numProcs);
    return numProcs;
}

MPI_Comm createSquareMesh(MPI_Comm comm);

#endif
