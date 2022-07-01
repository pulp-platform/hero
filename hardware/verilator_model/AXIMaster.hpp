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

#include "AXIDriver.hpp"

namespace KLAS_SIM
{

    template <typename AXIPortType>
    class AXIMaster : public AXIDriver<AXIPortType>
    {
        using typename AXIDriver<AXIPortType>::axi_ax_beat_t;
        using typename AXIDriver<AXIPortType>::axi_w_beat_t;
        using typename AXIDriver<AXIPortType>::axi_b_queue_entry_t;
        using typename AXIDriver<AXIPortType>::axi_r_queue_entry_t;
        using typename AXIDriver<AXIPortType>::beat_and_size_t;

        typedef typename AXIPortType::axi_addr_t axi_addr_t;

        using AXIDriver<AXIPortType>::port;
        using AXIDriver<AXIPortType>::create_ax_beats;
        using AXIDriver<AXIPortType>::beat_lower_byte;
        using AXIDriver<AXIPortType>::beat_upper_byte;

    private:
        typedef struct axi_r_buffered 
        {
            uint32_t data_length;
            uint8_t data[AXI_SW];
            bool is_last;
        } axi_r_buffered_t;

    private:
        std::queue<axi_ax_beat_t> aw_queue;
        std::queue<axi_w_beat_t> w_queue;
        std::queue<axi_r_buffered_t> r_queue;

        // a bit more high level. Takes into account that a write can be composed
        // by multiple AW beats. Same for reads.
        std::queue<axi_b_queue_entry_t> write_queue;
        std::queue<axi_r_queue_entry_t> read_queue;


        std::queue<axi_ax_beat_t> ar_queue;
        std::queue<bool> b_queue;

        std::queue<axi_ax_beat_t> aw_pending_queue;
        std::queue<axi_ax_beat_t> ar_pending_queue;
        std::queue<axi_w_beat_t> w_pending_queue;

        bool aw_wait;
        bool ar_wait;
        bool w_wait;

        uint32_t aw_beats_buffer_size;
        uint32_t w_beats_buffer_size;
        uint32_t b_beats_buffer_size;
        uint32_t ar_beats_buffer_size;
        uint32_t r_beats_buffer_size;

    public:

        bool has_aw_beat() 
        {
            return !aw_pending_queue.empty();
        }

        bool can_send_aw_beat()
        {
            return aw_beats_buffer_size == 0 || aw_queue.size() < aw_beats_buffer_size;
        }

        void send_aw_beat()
        {
            assert(!aw_pending_queue.empty() && can_send_aw_beat());
            axi_ax_beat_t &aw = aw_pending_queue.front();
            aw_queue.push(aw);
            aw_pending_queue.pop();
        }

        bool has_ar_beat()
        {
            return !ar_pending_queue.empty();
        }

        bool can_send_ar_beat()
        {
            return ar_beats_buffer_size == 0 || ar_queue.size() < ar_beats_buffer_size;
        }

        void send_ar_beat()
        {
            assert(!ar_pending_queue.empty() && can_send_ar_beat());
            axi_ax_beat_t &ar = ar_pending_queue.front();
            ar_queue.push(ar);
            ar_pending_queue.pop();
        }

        bool has_w_beat() 
        {
            return !w_pending_queue.empty();
        }

        bool can_send_w_beat()
        {
            return w_beats_buffer_size == 0 || w_queue.size() < w_beats_buffer_size;
        }

        void send_w_beat()
        {
            assert(!w_pending_queue.empty() && can_send_w_beat());
            axi_w_beat_t &w = w_pending_queue.front();
            w_queue.push(w);
            w_pending_queue.pop();
        }

        bool has_r_beat()
        {
            return !r_queue.empty();
        }

        bool consume_r_beat(uint8_t *data, uint32_t &data_length)
        {
            assert(has_r_beat());
            axi_r_buffered_t r = r_queue.front();
            data_length = std::min(data_length, r.data_length);
            if (data!=NULL) {
                memcpy(data, &(r.data[0]), data_length);
            }
            bool read_complete = r.is_last;
            r_queue.pop();
            return read_complete;
        }

        bool has_b_beat() 
        {
            return !b_queue.empty();
        }

        bool consume_b_beat()
        {
            bool res = b_queue.front();
            b_queue.pop();
            return res;
        }

        void set_aw_buffer(uint32_t aw_buffer_size)
        {
            aw_beats_buffer_size = aw_buffer_size;
        }

        void set_ar_buffer(uint32_t ar_buffer_size)
        {
            ar_beats_buffer_size = ar_buffer_size;
        }

        void set_w_buffer(uint32_t w_buffer_size)
        {
            w_beats_buffer_size = w_buffer_size;
        }

        void set_r_buffer(uint32_t r_buffer_size)
        {
            r_beats_buffer_size = r_buffer_size;
        }

        void set_b_buffer(uint32_t b_buffer_size)
        {
            b_beats_buffer_size = b_buffer_size;
        }

    public:
        AXIMaster(AXIPortType &port) : AXIDriver<AXIPortType>(port)
        {
            *port.aw_valid = 0;
            *port.aw_valid = 0;
            *port.w_valid = 0;

            *port.b_ready = 0;
            *port.r_ready = 0;

            aw_wait = false;
            ar_wait = false;
            w_wait = false;

            aw_beats_buffer_size = 0;
            ar_beats_buffer_size = 0;
            w_beats_buffer_size = 0;
            r_beats_buffer_size = 0;
            b_beats_buffer_size = 0;
        }

        void posedge()
        {
            aw_posedge();
            ar_posedge();
            w_posedge();
            b_posedge();
            r_posedge();
        }

        void negedge()
        {
            aw_negedge();
            ar_negedge();
            w_negedge();
            b_negedge();
            r_negedge();
        }

    public: /* interface */
        void write(axi_addr_t addr, uint8_t *data, uint32_t n_bytes, uint32_t offset)
        {
            // Create and send AW.
            uint32_t bytes_written = 0;
            axi_b_queue_entry_t write_queue_entry;

            std::queue<beat_and_size_t> aw_beats;
            create_ax_beats(addr, n_bytes, aw_beats);

            write_queue_entry.n_bursts = aw_beats.size();
            write_queue.push(write_queue_entry);

            //printf("Write: #aw: %u\n", aw_beats.size());
            uint32_t aw_cnt = 0;
            while (aw_beats.size() != 0)
            {
                uint32_t burst_bytes_written = 0;
                beat_and_size_t bs = aw_beats.front();
                aw_beats.pop();
                axi_ax_beat_t aw_beat = bs.beat;
                aw_pending_queue.push(aw_beat);

                aw_cnt++;
                //printf("Write: #w (aw_cnt: %u): %u; bytes_written: %u\n", aw_cnt, aw_beat.ax_len, bytes_written);
                
                // Send W beats filled with data from the `data` array.
                for (uint32_t i_beat = 0; i_beat <= aw_beat.ax_len; i_beat++)
                {
                    uint32_t lower_byte = beat_lower_byte(aw_beat, i_beat);
                    uint32_t upper_byte = beat_upper_byte(aw_beat, i_beat, bs.n_bytes);

                    axi_w_beat_t w_beat;
                    memset(&w_beat, 0, sizeof(axi_w_beat_t));

                    uint32_t beat_size = std::min(upper_byte - lower_byte, bs.n_bytes);

                    //printf("lb: %u; ub: %u; ub-lb: %u; bs.n_bytes: %u\n", lower_byte, upper_byte, upper_byte - lower_byte, bs.n_bytes);

                    memcpy(w_beat.w_data + lower_byte, data + offset + bytes_written + burst_bytes_written, beat_size);

                    for (uint32_t i_byte = lower_byte; i_byte < upper_byte && burst_bytes_written < bs.n_bytes; i_byte++)
                    {
                        w_beat.w_strb = w_beat.w_strb | ((1ul << (AXI_SW-1)) >> (AXI_SW - i_byte - 1));
                        //printf("%% i_byte: %u; w_strb: 0x%lx\n", i_byte, w_beat.w_strb);
                    }
                    if (i_beat == aw_beat.ax_len)
                    {
                        w_beat.w_last = 1;
                    }

                    w_pending_queue.push(w_beat);
                    burst_bytes_written += beat_size;
                }
                bytes_written += burst_bytes_written;
            }
            if (bytes_written != n_bytes)
            {
                printf("ERROR: bytes_written: %u; n_bytes: %u\n", bytes_written, n_bytes);
                assert(bytes_written == n_bytes);
            }
        }

        void read(axi_addr_t addr, uint32_t n_bytes)
        {
            axi_r_queue_entry_t read_queue_entry;
            std::queue<beat_and_size_t> ar_beats;

            create_ax_beats(addr, n_bytes, ar_beats);
            read_queue_entry.n_bursts = ar_beats.size();
            read_queue_entry.data_left = n_bytes;
            read_queue.push(read_queue_entry);

            while (ar_beats.size() != 0)
            {
                beat_and_size_t &bs = ar_beats.front();
                ar_beats.pop();
                axi_ax_beat_t ar_beat = bs.beat;
                ar_pending_queue.push(ar_beat);
            }
        }

    private:
        void aw_posedge()
        {
            if (aw_wait)
            {
                return;
            }

            *port.aw_valid = 0;

            if (aw_queue.empty())
            {
                return;
            }

            // send next AW beat
            axi_ax_beat_t &aw_beat = aw_queue.front();

            *port.aw_addr = aw_beat.ax_addr;
            *port.aw_prot = aw_beat.ax_prot;
            *port.aw_region = aw_beat.ax_region;
            *port.aw_len = aw_beat.ax_len;
            *port.aw_size = aw_beat.ax_size;
            *port.aw_burst = aw_beat.ax_burst;
            *port.aw_lock = aw_beat.ax_lock;
            *port.aw_atop = aw_beat.ax_atop;
            *port.aw_cache = aw_beat.ax_cache;
            *port.aw_qos = aw_beat.ax_qos;
            *port.aw_id = aw_beat.ax_id;
            *port.aw_user = aw_beat.ax_user;

            *port.aw_valid = 1;
            aw_queue.pop();
        }

        void aw_negedge()
        {
            //AW_READY can be function of AW_VALID, so let's see if we have it set already
            aw_wait = false;
            if (*port.aw_valid && !(*port.aw_ready))
            {
                aw_wait = true;
            }
        }

        void ar_posedge()
        {
            if (ar_wait)
            {
                return;
            }

            *port.ar_valid = 0;

            if (ar_queue.empty())
            {
                return;
            }

            // send next AR beat
            axi_ax_beat_t &ar_beat = ar_queue.front();

            *port.ar_addr = ar_beat.ax_addr;
            *port.ar_prot = ar_beat.ax_prot;
            *port.ar_region = ar_beat.ax_region;
            *port.ar_len = ar_beat.ax_len;
            *port.ar_size = ar_beat.ax_size;
            *port.ar_burst = ar_beat.ax_burst;
            *port.ar_lock = ar_beat.ax_lock;
            *port.ar_cache = ar_beat.ax_cache;
            *port.ar_qos = ar_beat.ax_qos;
            *port.ar_id = ar_beat.ax_id;
            *port.ar_user = ar_beat.ax_user;

            *port.ar_valid = 1;
            ar_queue.pop();
        }

        void ar_negedge()
        {
            //AR_READY can be function of AR_VALID, so let's see if we have it set already
            ar_wait = false;
            if (*port.ar_valid && !(*port.ar_ready))
            {
                ar_wait = true;
            }
        }

        void w_posedge()
        {
            if (w_wait)
            {
                return;
            }

            *port.w_valid = 0;
            *port.w_last = 0;

            if (w_queue.empty())
            {
                return;
            }

            // send next W beat
            axi_w_beat_t &w_beat = w_queue.front();

            //copy data
            memcpy(port.w_data, w_beat.w_data, AXI_SW);

            *port.w_strb = w_beat.w_strb;
            *port.w_user = w_beat.w_user;
            *port.w_last = w_beat.w_last;

            *port.w_valid = 1;
            w_queue.pop();
        }

        void w_negedge()
        {
            //AW_READY can be function of AW_VALID, so let's see if we have it set already
            w_wait = false;
            if (*port.w_valid && !(*port.w_ready))
            {
                w_wait = true;
            }
        }

        void b_posedge()
        {
            bool can_accept_b = b_beats_buffer_size == 0 || b_queue.size() < b_beats_buffer_size;

            if (*port.b_valid && can_accept_b)
            {
                assert(!write_queue.empty());
                axi_b_queue_entry_t &entry = write_queue.front();

                entry.n_bursts--;
                bool is_complete = entry.n_bursts == 0;

                *port.b_ready = 1;
                if (is_complete) {
                    write_queue.pop();
                }

                b_queue.push(is_complete);
            }
        }

        void b_negedge()
        {
            //nothing to do here
        }

        void r_posedge()
        {
            bool can_accept_r = r_beats_buffer_size == 0 || r_queue.size() < r_beats_buffer_size;

            if (*port.r_valid && can_accept_r)
            {
                assert(!read_queue.empty());
                axi_r_queue_entry_t &entry = read_queue.front();

                uint32_t data_size = std::min((uint32_t)AXI_SW, entry.data_left);
                uint32_t completed_burst = (*port.r_last == 1) ? 1 : 0;
                
                *port.r_ready = 1;

                entry.n_bursts -= completed_burst;
                entry.data_left -= data_size;
                bool is_complete = entry.n_bursts == 0;
                if (is_complete) read_queue.pop();

                axi_r_buffered_t r_buff;
                r_buff.data_length = data_size;
                memcpy(r_buff.data, port.r_data, data_size);
                r_buff.is_last = is_complete;
                r_queue.push(r_buff);
            }
        }

        void r_negedge()
        {
            //nothing to do here
        }
    };

} // namespace PsPIN
