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
        MPI_xSend(data, count, type, (root + numProcs / 2) % numProcs, 0, comm);
        // cout << getGlobalRank() << " sends\n";
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


void chainSend(int *data, int index, MPI_Datatype type, int root, MPI_Comm comm, direction dir) {
    if ((root <= 0 && dir == LEFT) || (root >= getNumProcs(comm) - 1 && dir == RIGHT)) {
        return;
    }

    int localRank = getLocalRank(comm);
    if (localRank == root) {
        MPI_xSend(&data[index], 1, type, root + dir, index, comm);
        // cout << getGlobalRank() << " sends\n";
    }
    else if (localRank == root + dir) {
        MPI_Recv(&data[index], 1, type, root, index, comm, MPI_STATUS_IGNORE);
    }

    chainSend(data, index, type, root + dir, comm, dir);
}

void broadcastLinear(int *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    if (root == 0) {
        for (int i = 0; i < count; i++) {
            chainSend(data, i, type, root, comm, RIGHT);
        }
    }
    else if (root == getNumProcs(comm) - 1) {
        for (int i = 0; i < count; i++) {
            chainSend(data, i, type, root, comm, LEFT);
        }
    }
    else {
        for (int i = 0; i < count; i++) {
            chainSend(data, i, type, root, comm, RIGHT);
            chainSend(data, i, type, root, comm, LEFT);
        }
    }
}

void broadcastPlanar(int *data, int count, MPI_Datatype type, int root, MPI_Comm comm) {
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


void chainReduce(int *send_data, int *recv_data, int index, MPI_Datatype type, int (*op)(int, int), int root, MPI_Comm comm, direction dir) {
    if ((root <= 0 && dir == LEFT) || (root >= getNumProcs(comm) - 1 && dir == RIGHT)) {
        recv_data[index] = send_data[index];
        return;
    }

    chainReduce(send_data, recv_data, index, type, op, root + dir, comm, dir);

    int localRank = getLocalRank(comm);
    if (localRank == root) {
        int temp;
        MPI_Recv(&temp, 1, type, root + dir, index, comm, MPI_STATUS_IGNORE);
        recv_data[index] = op(send_data[index], temp);
    }
    else if (localRank == root + dir) {
        MPI_xSend(&recv_data[index], 1, type, root, index, comm);
        // cout << getGlobalRank() << " sends\n";
    }
}

void reduceLinear(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), int root, MPI_Comm comm) {
    if (root == 0) {
        for (int i = 0; i < count; i++) {
            chainReduce(send_data, recv_data, i, type, op, root, comm, RIGHT);
        }
    }
    else if (root == getNumProcs(comm) - 1) {
        for (int i = 0; i < count; i++) {
            chainReduce(send_data, recv_data, i, type, op, root, comm, LEFT);
        }
    }
    else {
        for (int i = 0; i < count; i++) {
            chainReduce(send_data, recv_data, i, type, op, root, comm, RIGHT);
            chainReduce(recv_data, recv_data, i, type, op, root, comm, LEFT);
        }
    }
}

void reducePlanar(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), int root, MPI_Comm comm) {
    // Get mesh dimensions
    int dims[2], periods[2], procCoords[2];
    MPI_Cart_get(comm, 2, dims, periods, procCoords);
    int rootRow = root / dims[0], rootCol = root % dims[0];
    
    // split communicator into row and column ones
    MPI_Comm rowComm, colComm;
    MPI_Comm_split(comm, procCoords[0], procCoords[1], &rowComm);
    MPI_Comm_split(comm, procCoords[1], procCoords[0], &colComm);

    int *temp = new int[count];
    reduceLinear(send_data, temp, count, type, op, rootRow, colComm);

    int localRank = getLocalRank(comm);
    if (localRank / dims[0] == rootRow ) {
        reduceLinear(temp, recv_data, count, type, op, rootCol, rowComm);
    }
}


void allReduceLinear(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), MPI_Comm comm) {
    int root = getNumProcs(comm) / 2;
    reduceLinear(send_data, recv_data, count, MPI_INT, op, root, comm);
    broadcastLinear(recv_data, count, MPI_INT, root, comm);
}

void allReducePlanar(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), MPI_Comm comm) {
    // Get mesh dimensions
    int dims[2], periods[2], procCoords[2];
    MPI_Cart_get(comm, 2, dims, periods, procCoords);

    // split communicator into row and column ones
    MPI_Comm rowComm, colComm;
    MPI_Comm_split(comm, procCoords[0], procCoords[1], &rowComm);
    MPI_Comm_split(comm, procCoords[1], procCoords[0], &colComm);

    int *temp = new int[count];
    allReduceLinear(send_data, temp, count, type, op, colComm);
    allReduceLinear(temp, recv_data, count, type, op, rowComm);
}
