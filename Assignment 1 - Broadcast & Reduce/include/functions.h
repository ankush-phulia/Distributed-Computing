#ifndef FUNCTIONS_H
#define FUNCTIONS_H

#include "util.h"

void broadcastLinear(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm);
void broadcastPlanar(void *data, int count, MPI_Datatype type, int root, MPI_Comm comm);

#endif
