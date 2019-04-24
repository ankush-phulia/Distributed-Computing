#include "functions.h"
#include "util.h"

#include <string>
#include <unordered_map>

using namespace std;

unordered_map<string, int (*)(int, int)> operator_map = {
    {"sum", sum}, {"prod", prod}, {"min", min}, {"max", max}, 
};

void printResult(int *result, int size, int rank) {
    if (getGlobalRank() == rank) {
        for (int i = 0; i < size; i++) {
            cout << result[i] << " ";
        }
        cout << endl;
    }
}

int main(int argc, char *argv[]) {
    MPI_Init(&argc, &argv);
    MPI_Comm mesh = createSquareMesh(MPI_COMM_WORLD);

    int size = 5;
    int data[size] = { 1, 2, 3, 4, 5 };
    int result[size] = { 0, 0, 0, 0, 0 };

    if (string(argv[1]) == "broadcast") {
        int root = stoi(argv[2]);
        if (getGlobalRank() == root) {
            data[0] = data[1] = data[2] = 10;
        }
        
        broadcastPlanar(data, size, MPI_INT, stoi(argv[2]), mesh);
        printResult(data, size, 3);
    }
    else if (string(argv[1]) == "reduce") {
        int root = stoi(argv[2]);
        reducePlanar(data, result, size, MPI_INT, operator_map[string(argv[3])], root, mesh);
        printResult(result, size, root);
    }
    else if (string(argv[1]) == "allreduce") {
        allReducePlanar(data, result, size, MPI_INT, operator_map[string(argv[2])], mesh);
        printResult(result, size, 0);
    }

    MPI_Finalize();
}