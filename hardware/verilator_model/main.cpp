#include "klas_vlt.h"
#include "Vpulp_cluster.h"
#include <pthread.h>

int main(int argc, char *argv[]) {

    cout << "enter main" << endl;
    pthread_t thr_sim_ctrl;

    auto *tb = new klas_vlt<Vpulp_cluster>(argc, argv);

    tb->klas_run();

    return 0;
}
