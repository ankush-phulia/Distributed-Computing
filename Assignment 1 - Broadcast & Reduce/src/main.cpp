#include "functions.h"
#include "util.h"

using namespace std;

int main(int argc, char *argv[]) {
    MPI_Init(&argc, &argv);

    MPI_Comm mesh = createSquareMesh(MPI_COMM_WORLD);

    int data = 1;
    broadcastPlanar(&data, 1, MPI_INT, 0, mesh);

    MPI_Finalize();
}