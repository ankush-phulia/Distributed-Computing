#include "functions.h"
#include "util.h"

#include <string>
#include <unordered_map>

using namespace std;

unordered_map<string, int (*)(int, int)> operator_map = {
    {"sum", sum}, {"prod", prod}, {"min", min}, {"max", max}, 
};

int main(int argc, char *argv[]) {
    MPI_Init(&argc, &argv);
    MPI_Comm mesh = createSquareMesh(MPI_COMM_WORLD);

    int data = 1;
    int result = 0;

    if (string(argv[1]) == "bcast") {
        broadcastPlanar(&data, 1, MPI_INT, stoi(argv[2]), mesh);
    }
    else if (string(argv[1]) == "reduce") {
        int root = stoi(argv[2]);
        reducePlanar(&data, &result, 1, MPI_INT, operator_map[string(argv[3])], root, mesh);
        if (getGlobalRank() == root) {
            cout << result << endl;
        }
    }

    MPI_Finalize();
}