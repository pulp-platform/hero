#include "klas_vlt.h"
#include "Vpulp_cluster.h"

int sc_main(int argc, char *argv[]) {

    auto *tb = new klas_vlt<Vpulp_cluster>(argc, argv);

    tb->gdriver_run();
    tb->gdriver_finish();

    return 0;
}
