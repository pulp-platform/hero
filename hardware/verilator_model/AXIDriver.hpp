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

#include <functional>

#include "AXIPort.hpp"

namespace KLAS_SIM
{
    template <typename AXIPortType>
    class AXIDriver
    {
        typedef typename AXIPortType::axi_addr_t axi_addr_t;
        typedef typename AXIPortType::axi_strb_t axi_strb_t;
        typedef typename AXIPortType::axi_prot_t axi_prot_t;
        typedef typename AXIPortType::axi_region_t axi_region_t;
        typedef typename AXIPortType::axi_len_t axi_len_t;
        typedef typename AXIPortType::axi_size_t axi_size_t;
        typedef typename AXIPortType::axi_burst_t axi_burst_t;
        typedef typename AXIPortType::axi_lock_t axi_lock_t;
        typedef typename AXIPortType::axi_atop_t axi_atop_t;
        typedef typename AXIPortType::axi_cache_t axi_cache_t;
        typedef typename AXIPortType::axi_qos_t axi_qos_t;
        typedef typename AXIPortType::axi_id_t axi_id_t;
        typedef typename AXIPortType::axi_user_t axi_user_t;

    protected:
        typedef struct axi_ax_beat
        {
            axi_id_t ax_id;
            axi_addr_t ax_addr;
            axi_len_t ax_len;
            axi_size_t ax_size;
            axi_burst_t ax_burst;
            axi_lock_t ax_lock;
            axi_cache_t ax_cache;
            axi_prot_t ax_prot;
            axi_qos_t ax_qos;
            axi_region_t ax_region;
            axi_atop_t ax_atop; // Only defined on the AW channel.
            axi_user_t ax_user;

            uint32_t offset; //bytes already received
        } axi_ax_beat_t;

        typedef struct axi_w_beat
        {
            uint8_t w_data[AXI_SW];
            axi_strb_t w_strb;
            axi_user_t w_user;
            uint8_t w_last;
        } axi_w_beat_t;

        typedef struct axi_b_beat
        {
            uint8_t b_resp;
            axi_id_t b_id;
            axi_user_t b_user;
        } axi_b_beat_t;

        typedef struct axi_r_beat
        {
            uint8_t r_resp;
            uint8_t r_last;
            axi_id_t r_id;
            axi_user_t r_user;
            uint8_t r_data[AXI_SW];
        } axi_r_beat_t;

        typedef struct axi_b_queue_entry
        {
            uint32_t n_bursts;
            void *b_callback_arg;
        } axi_b_queue_entry_t;

        typedef struct axi_r_queue_entry
        {
            uint32_t data_left;
            uint32_t n_bursts;
            void *r_callback_arg;
        } axi_r_queue_entry_t;

        typedef struct beat_and_size
        {
            axi_ax_beat_t beat;
            uint32_t n_bytes;
        } beat_and_size_t;

    public:
        AXIDriver<AXIPortType>(AXIPortType &port) : port(port)
        {
            *port.aw_valid = 0;
            *port.w_valid = 0;
            *port.b_ready = 0;
            *port.ar_valid = 0;
            *port.r_ready = 0;
        }

        virtual void posedge() = 0;
        virtual void negedge() = 0;

    protected:
        AXIPortType &port;

    protected:
        uint32_t axi_num_bytes(axi_size_t size)
        {
            return 1 << size;
        }

        axi_addr_t axi_aligned_address(axi_addr_t addr, axi_size_t size)
        {
            return (addr / axi_num_bytes(size)) * axi_num_bytes(size);
        }

        axi_addr_t beat_addr(axi_ax_beat_t ax, uint32_t i_beat)
        {
            if (i_beat == 0)
                return ax.ax_addr;
            else
                return axi_aligned_address(ax.ax_addr, ax.ax_size) + i_beat * (1 << ax.ax_size);
        }

        uint32_t beat_lower_byte(axi_ax_beat_t ax, uint32_t i_beat)
        {
            axi_addr_t addr = beat_addr(ax, i_beat);
            return addr - (addr / AXI_SW) * AXI_SW;
        }

        uint32_t beat_upper_byte(axi_ax_beat_t ax, uint32_t i_beat, uint32_t n_bytes)
        {
            if (i_beat == 0)
            {
                return axi_aligned_address(ax.ax_addr, ax.ax_size) + (1 << ax.ax_size) - (ax.ax_addr / AXI_SW) * AXI_SW;
            }
            else if (i_beat == ax.ax_len)
            {
                return n_bytes - (AXI_SW - beat_lower_byte(ax, 0)) - (ax.ax_len - 1) * AXI_SW;
            }
            else
            {
                return beat_lower_byte(ax, i_beat) + (1 << ax.ax_size);
            }
        }

        uint64_t page_num(axi_addr_t addr)
        {
            return addr >> 12;
        }

        void create_ax_beats(axi_addr_t addr, uint32_t n_bytes, std::queue<beat_and_size_t> &ax_beats)
        {
            uint64_t n_beats;
            uint32_t bytes_in_first_beat, bytes_in_last_beat;
            size_t ax_size;

            // Iteratively create Ax beats until all bytes have been transferred.
            while (n_bytes > 0)
            {
                axi_ax_beat_t ax_beat;
                uint32_t bytes_in_burst;

                memset(&ax_beat, 0, sizeof(axi_ax_beat_t));

                ax_beat.ax_addr = addr;
                ax_beat.ax_burst = AXI_BURST_INCR;

                // Determine size of each beat.
                if (n_bytes > AXI_SW || (addr >> ((uint32_t)log2(AXI_SW))) != (addr + n_bytes - 1) >> ((uint32_t)log2(AXI_SW)))
                {
                    // If the number of bytes exceeds the data bus width or the first byte is not on the same
                    // AXI line as the last byte, we have to write multiple beats.  In this case, the burst must
                    // use the full data bus.
                    ax_beat.ax_size = log2(AXI_SW);
                }
                else
                {
                    // If the number of bytes is less or equal to the data bus width, a single beat is
                    // sufficient.  The size of the beat depends on the address, which determines the lower byte
                    // lane; all bytes must fit into the beat.
                    // The smallest possible value is the number of bytes to be transferred.
                    ax_beat.ax_size = log2(n_bytes);
                    // If the resulting upper byte lane is not high enough to accommodate all bytes, increment
                    // the size.
                    while (beat_upper_byte(ax_beat, 0, n_bytes) - beat_lower_byte(ax_beat, 0) < n_bytes)
                    {
                        assert(ax_beat.ax_size < log2(AXI_SW));
                        ax_beat.ax_size++;
                    }
                }

                // Calculate bytes per beat and total number of beats.
                bytes_in_first_beat = AXI_SW - (addr % AXI_SW);
                if (n_bytes <= bytes_in_first_beat)
                {
                    bytes_in_first_beat = n_bytes;
                    n_beats = 1;
                }
                else
                {
                    n_beats = 1 + ceil(((double)(n_bytes - bytes_in_first_beat)) / AXI_SW);
                    bytes_in_last_beat = n_bytes - bytes_in_first_beat - AXI_SW * (n_beats - 2);
                }

                if (page_num(addr) != page_num(addr + n_bytes - 1))
                {
                    bytes_in_burst = 4096 - (addr & 0xFFF);
                    create_ax_beats(addr, bytes_in_burst, ax_beats);
                }
                else
                {
                    beat_and_size_t bs;
                    bytes_in_burst = bytes_in_first_beat;
                    if (n_beats > 256)
                    {
                        n_beats = 256;
                        bytes_in_last_beat = AXI_SW;
                    }
                    if (n_beats > 1)
                    {
                        bytes_in_burst += (n_beats - 2) * AXI_SW + bytes_in_last_beat;
                    }
                    ax_beat.ax_len = n_beats - 1;
                    bs.beat = ax_beat;
                    bs.n_bytes = bytes_in_burst;
                    ax_beats.push(bs);
                }
                addr += bytes_in_burst;
                n_bytes -= bytes_in_burst;
            }
        }
    };

} // namespace PsPIN
