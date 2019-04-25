#ifndef UTIL_H
#define UTIL_H

#include "mpix.h"

enum direction { LEFT = -1, RIGHT = 1 }; 

// MPI Operations 
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


// Reduce operators
inline int sum(int op1, int op2) {
    return op1 + op2;
}

inline int prod(int op1, int op2) {
    return op1 * op2;
}

inline int min(int op1, int op2) {
    return op1 < op2 ? op1 : op2;
}

inline int max(int op1, int op2) {
    return op1 < op2 ? op2 : op1;
}

#endif
