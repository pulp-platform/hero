// Copyright 2020 ETH Zurich
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#pragma once
#include <stdint.h>

#define VERILATOR_HAS_TRACE
#define SIM_PRINT(FORMAT, ...) printf ("[%lu][%s:%u]: " FORMAT, sim_time(), __FILE__, __LINE__, ## __VA_ARGS__)

class SimModule {
public:
    virtual void posedge() = 0;    
    virtual void negedge() = 0;    

    virtual void print_stats() = 0;

public:
    uint64_t sim_time() {
        return 0; // sc_time_stamp();
    }
};
