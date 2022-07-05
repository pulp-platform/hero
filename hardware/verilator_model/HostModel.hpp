#include "AXIPort.hpp"
#include "verilated.h"
#include "SimModule.hpp"
#include "AXIMaster.hpp"

#include <queue>
#include <vector>
#include <unordered_map>
#include <stdio.h>

namespace KLAS_SIM {
    template<typename AXIPortType>
    class HostModel : public SimModule {
    public:
        typedef typename AXIPortType::axi_addr_t axi_addr_t;

    public:
        HostModel(AXIPortType &axi_mst) : axi_driver(axi_mst) {
        }

        int write_word(axi_addr_t addr, uint8_t *data) {
            axi_driver.write(addr, data, 4, 0);

            return 0;
        }

        // implement API
        void posedge(void) {
            progress_axi_writes(); // write if axi write queue is not empty
            axi_driver.posedge();  // update axi write interface
            progress_axi_write_responses(); // update response channel
        }
        void negedge(void) {}
        void print_stats(void) {}

    private:
        std::queue<&void>   cmdq;

    private:
        AXIMaster<AXIPortType> axi_driver;
                
    };
}
