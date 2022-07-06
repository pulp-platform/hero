#include "klas_vlt.h"
#include "Vtop.h"


int sc_main(int argc, char *argv[]) {
    cout << "enter main" << endl;

    auto *tb = new klas_vlt<Vtop>(argc, argv);
    tb->klas_run();

    return 0;
}
