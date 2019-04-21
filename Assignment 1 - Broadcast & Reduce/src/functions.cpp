#include "functions.h"

#include <iostream>

using namespace std;

void broadcastLinearRec(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    int numProcs = getNumProcs(comm);    
    if (numProcs <= 1) {
        return;
    }

    // Send/Receive message from 0th to (n/2)th process
    int localRank = getLocalRank(comm);
    if (localRank == root) {
        MPI_Send(data, count, type, (root + numProcs / 2) % numProcs, 0, comm);
        cout << getGlobalRank() << " sends\n";
    }
    else if (localRank == (root + numProcs / 2) % numProcs) {
        MPI_Recv(data, count, type, root, 0, comm, MPI_STATUS_IGNORE);
    }

    // Split communicator into halves
    MPI_Comm halfComm;
    MPI_Comm_split(comm, ((localRank - root + numProcs) % numProcs < numProcs / 2), localRank, &halfComm);
    
    // Recursively spread message in each half
    broadcastLinearRec(data, count, type, 0, halfComm);
}

void broadcastPlanarRec(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    // Get mesh dimensions
    int dims[2], periods[2], procCoords[2];
    MPI_Cart_get(comm, 2, dims, periods, procCoords);
    
    // split communicator into row and column ones
    MPI_Comm rowComm, colComm;
    int rootRow = root / dims[0], rootCol = root % dims[0];

    // make the root as 0, 0 - so that its row is row 0
    MPI_Comm_split(comm, procCoords[0], (procCoords[1] - rootCol + dims[1]) % dims[1], &rowComm);
    MPI_Comm_split(comm, procCoords[1], (procCoords[0] - rootRow + dims[0]) % dims[0], &colComm);
    
    int localRank = getLocalRank(comm);
    if (localRank / dims[0] == rootRow) { // same row, receive data from 0th
        broadcastLinearRec(data, count, type, 0, rowComm);
    }
    // spread info from row 0 to the others, column-wise
    broadcastLinearRec(data, count, type, 0, colComm);
}


void chainSend(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm, direction dir) {
    if ((root <= 0 && dir == LEFT) || (root >= getNumProcs(comm) - 1 && dir == RIGHT)) {
        return;
    }

    int localRank = getLocalRank(comm);
    if (localRank == root) {
        MPI_Send(data, count, type, root + dir, 0, comm);
        cout << getGlobalRank() << " sends\n";
    }
    else if (localRank == root + dir) {
        MPI_Recv(data, count, type, root, 0, comm, MPI_STATUS_IGNORE);
    }

    chainSend(data, count, type, root + dir, comm, dir);
}

void broadcastLinear(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    if (root == 0) {
        chainSend(data, count, type, root, comm, RIGHT);
    }
    else if (root == getNumProcs(comm) - 1) {
        chainSend(data, count, type, root, comm, LEFT);
    }
    else {
        chainSend(data, count, type, root, comm, RIGHT);
        chainSend(data, count, type, root, comm, LEFT);
    }
}

void broadcastPlanar(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    // Get mesh dimensions
    int dims[2], periods[2], procCoords[2];
    MPI_Cart_get(comm, 2, dims, periods, procCoords);
    int rootRow = root / dims[0], rootCol = root % dims[0];
    
    // split communicator into row and column ones
    MPI_Comm rowComm, colComm;
    MPI_Comm_split(comm, procCoords[0], procCoords[1], &rowComm);
    MPI_Comm_split(comm, procCoords[1], procCoords[0], &colComm);

    int localRank = getLocalRank(comm);
    if (localRank / dims[0] == rootRow ) {
        broadcastLinear(data, count, type, rootCol, rowComm);
    }
    broadcastLinear(data, count, type, rootRow, colComm);
}
