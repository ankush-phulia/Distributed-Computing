#ifndef FUNCTIONS_H
#define FUNCTIONS_H

#include "util.h"

void broadcastLinear(int *data, int count, MPI_Datatype type, int root, MPI_Comm comm);
void broadcastPlanar(int *data, int count, MPI_Datatype type, int root, MPI_Comm comm);

void reduceLinear(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), int root, MPI_Comm comm);
void reducePlanar(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), int root, MPI_Comm comm);

void allReduceLinear(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), MPI_Comm comm);
void allReducePlanar(int *send_data, int *recv_data, int count, MPI_Datatype type, int (*op)(int, int), MPI_Comm comm);

#endif
