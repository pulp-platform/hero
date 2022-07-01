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
    class HOST_MODEL : public SimModule {
    public:
        typedef typename AXIPortType::axi_addr_t axi_addr_t;

    public:
        HOST_MODEL(AXIPortType &axi_mst) {
            this->axi_driver = axi_mst;
        }


        int write_word(axi_addr_t addr, uint8_t *data) {
            axi_driver.write(addr, data, 4, 0);

            return 0;
        }

    private:
        AXIMaster<AXIPortType> axi_driver;
                
    };
}
