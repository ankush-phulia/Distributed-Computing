#include "functions.h"

#include <iostream>

using namespace std;

void broadcastLinear(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    int numProcs = getNumProcs(comm);    
    if (numProcs <= 1) {
        return;
    }

    // Send/Receive message from 0th to (n/2)th process
    int localRank = getLocalRank(comm);
    if (localRank == root) {
        MPI_Send(data, count, type, (root + numProcs / 2) % numProcs, 0, comm);
        cout << getGlobalRank() << " sends" << endl;
    }
    else if (localRank == (root + numProcs / 2) % numProcs) {
        MPI_Recv(data, count, type, root, 0, comm, MPI_STATUS_IGNORE);
    }

    // Split communicator into halves
    MPI_Comm halfComm;
    MPI_Comm_split(comm, ((localRank - root + numProcs) % numProcs < numProcs / 2), localRank, &halfComm);
    
    // Recursively spread message in each half
    broadcastLinear(data, count, type, 0, halfComm);
}

void broadcastPlanar(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    // Get mesh dimensions
    int dims[2], periods[2], procCoords[2];
    MPI_Cart_get(comm, 2, dims, periods, procCoords);
    
    // split communicator into row and column ones
    MPI_Comm rowComm, colComm;
    int rootRow = root / dims[0], rootCol = root % dims[0];

    // make the root as 0, 0 - so that its row is row 0
    MPI_Comm_split(comm, procCoords[0], (procCoords[1] - rootCol + dims[1]) % dims[1], &rowComm);
    MPI_Comm_split(comm, procCoords[1], (procCoords[0] - rootRow + dims[0]) % dims[0], &colComm);
    
    int localRank = getLocalRank(comm);;
    if (localRank / dims[0] == rootRow) { // same row, receive data from 0th
        broadcastLinear(data, count, type, 0, rowComm);
    }
    // spread info from row 0 to the others, column-wise
    broadcastLinear(data, count, type, 0, colComm);
}

