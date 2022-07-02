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

#include "verilated.h"
#include "verilated_vcd_c.h"
#include <systemc.h>    // SystemC global header

#include "SimModule.hpp"

#include <vector>
#include <functional>
#include <systemc.h>    // SystemC global header

template<class T>
class SimControl
{
private:
    T *tb;
    VerilatedVcdC *m_trace;
    uint64_t m_tickcount;
    sc_signal<bool> rst_ni;
    bool trace;
    std::vector<std::reference_wrapper<SimModule>> sim_modules;

public:
    SimControl(T *tb, const char *trace_filename) : tb(tb)
    {
        m_tickcount = 0;

        tb->rst_ni(rst_ni);
#ifdef VERILATOR_HAS_TRACE
        trace = trace_filename != NULL;

        if (trace)
        {
            Verilated::traceEverOn(true);

            m_trace = new VerilatedVcdC;

            // Initialize trace
            tb->trace(m_trace, 99);
            m_trace->open(trace_filename);
            printf("trace on!\n");
        }
#else
        printf("trace off!\n");
        trace = false;
#endif
    }

    ~SimControl()
    {
#ifdef VERILATOR_HAS_TRACE
        m_trace->flush();
        m_trace->close();
#endif
    }

    std::vector<std::reference_wrapper<SimModule>>& get_modules()
    {
        return sim_modules;
    }

    void add_module(SimModule &module) 
    {
        sim_modules.push_back(std::ref(module));
    }

    // simulated time (ps)
    uint64_t time() 
    {
        return m_tickcount*1000;
    }

    void reset()
    {
        //tb->rst_ni = 0;
        //for (int i = 0; i < 4; i++)
        //{
        //    tb->clk_i = 1;
        //    tb->eval();
        //    tb->clk_i = 0;
        //    tb->eval();
        //}
        //tb->rst_ni = 1;
        //
        this->rst_ni = false;
        sc_start(100, SC_NS);
        this->rst_ni = true ;
    }
    
    void run_single()
    {
        m_tickcount++;

        //tb->clk_i = 1;
        //tb->eval();
        tb->clk_i->posedge_event();

#ifdef VERILATOR_HAS_TRACE
        if (trace)
        {
            m_trace->dump(1000 * m_tickcount);
        }
#endif
        run_sim_modules_posedge();

        //// Allow any combinatorial logic to settle before we tick
        //// the clock.  This becomes necessary in the case where
        //// we may have modified or adjusted the inputs prior to
        //// coming into here, since we need all combinatorial logic
        //// to be settled before we call for a clock tick.
        //tb->clk_i = 1;
        //tb->eval();

#ifdef VERILATOR_HAS_TRACE
        if (trace)
        {
            m_trace->dump(1000 * m_tickcount + 250);
            m_trace->flush();
        }
#endif

        //tb->clk_i = 0;
        //tb->eval();
        tb->clk_i->negedge_event();

#ifdef VERILATOR_HAS_TRACE
        if (trace)
        {
            m_trace->dump(1000 * m_tickcount + 500);
        }
#endif
        
        run_sim_modules_negedge();

        //tb->clk_i = 0;
        //tb->eval();

#ifdef VERILATOR_HAS_TRACE
        if (trace)
        {
            m_trace->dump(1000 * m_tickcount + 750);
        }
#endif

    }

    void run_all()
    {
        while (!done())
        {
            run_single();
        }
    }

    bool done() 
    {
        return Verilated::gotFinish();
    }

private:
    void run_sim_modules_posedge()
    {
        for (auto it=sim_modules.begin(); it!=sim_modules.end(); ++it)
        {
            it->get().posedge();
        }
    }

    void run_sim_modules_negedge()
    {
        for (auto it=sim_modules.begin(); it!=sim_modules.end(); ++it)
        {
            it->get().negedge();
        }
    }


};
