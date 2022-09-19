#include "traffic_gen_api.h"

/* Parameters mapping */
static inline void traffic_gen_wrapper_map_params(
  traffic_gen_wrapper_struct *wrapper, 
  hwpe_l1_ptr_struct *l1_traffic_gen_buffer, 
  hwpe_traffic_gen_workload_params *params) 
{
  /* Extract parameters */

  uint32_t width                                    = params->standard.width;
  uint32_t height                                   = params->standard.height;
  uint32_t stripe_height                            = params->standard.stripe_height;
  uint32_t stim_dim                                 = params->standard.stim_dim;
  uint32_t stripe_length                            = params->standard.stripe_length;
  uint32_t buffer_dim                               = params->standard.buffer_dim;
  uint32_t buffer_stride                            = params->standard.buffer_stride;
  uint32_t data_stride                              = params->standard.data_stride;

  uint32_t n_total_reqs                             = params->n_total_reqs; 
  uint32_t t_ck_reqs                                = params->t_ck_reqs; 
  uint32_t t_ck_idle                                = params->t_ck_idle;
  uint32_t max_buffer_dim                           = params->max_buffer_dim;
  uint32_t n_reps                                   = params->n_reps;
  uint32_t n_tcdm_banks                             = params->n_tcdm_banks;

  /* Streamer */

  // Read requests
  wrapper->r_reqs.params.width                         = max_buffer_dim;
  wrapper->r_reqs.params.height                        = 1;
  wrapper->r_reqs.params.stripe_height                 = 1;
  wrapper->r_reqs.params.stim_dim                      = n_total_reqs;
  wrapper->r_reqs.params.stripe_length                 = n_total_reqs;
  wrapper->r_reqs.params.buffer_dim                    = max_buffer_dim;

  wrapper->r_reqs.params.buffer_stride                 = 0;
  wrapper->r_reqs.params.data_stride                   = 1;
  
  wrapper->r_reqs.addr_gen.trans_size                  = n_total_reqs;
  wrapper->r_reqs.addr_gen.line_stride                 = 0; 
  wrapper->r_reqs.addr_gen.line_length                 = max_buffer_dim;
  wrapper->r_reqs.addr_gen.feat_stride                 = 0; 
  wrapper->r_reqs.addr_gen.feat_length                 = n_reps; 
  wrapper->r_reqs.addr_gen.feat_roll                   = 0; 
  wrapper->r_reqs.addr_gen.loop_outer                  = 0; 
  wrapper->r_reqs.addr_gen.realign_type                = 0; 
  wrapper->r_reqs.addr_gen.step                        = 4;

  // Write requests
  wrapper->w_reqs.params.width                         = (t_ck_idle>0) ? (n_total_reqs/t_ck_reqs) : 1;
  wrapper->w_reqs.params.height                        = 1;
  wrapper->w_reqs.params.stripe_height                 = 1;
  wrapper->w_reqs.params.stim_dim                      = (t_ck_idle>0) ? (n_total_reqs/t_ck_reqs) : 1;
  wrapper->w_reqs.params.stripe_length                 = 1;
  wrapper->w_reqs.params.buffer_dim                    = n_tcdm_banks; // proportional to n_tcdm_banks so to have buffers aligned and model different access patterns

  wrapper->w_reqs.params.buffer_stride                 = 0;
  wrapper->w_reqs.params.data_stride                   = 1;

  wrapper->w_reqs.addr_gen.trans_size                  = (t_ck_idle>0) ? (n_total_reqs/t_ck_reqs + 1) : (1+1); 
  wrapper->w_reqs.addr_gen.line_stride                 = 0; 
  wrapper->w_reqs.addr_gen.line_length                 = (t_ck_idle>0) ? (n_total_reqs/t_ck_reqs) : 1; 
  wrapper->w_reqs.addr_gen.feat_stride                 = 0; 
  wrapper->w_reqs.addr_gen.feat_length                 = 1; 
  wrapper->w_reqs.addr_gen.feat_roll                   = 0; 
  wrapper->w_reqs.addr_gen.loop_outer                  = 0; 
  wrapper->w_reqs.addr_gen.realign_type                = 0; 
  wrapper->w_reqs.addr_gen.step                        = 4;  

  // Assign buffer pointers
  wrapper->r_reqs.tcdm.ptr = (DEVICE_PTR)l1_traffic_gen_buffer->ptr; 
  wrapper->w_reqs.tcdm.ptr = (DEVICE_PTR)l1_traffic_gen_buffer->ptr;

  /* Controller */

  // FSM
  wrapper->ctrl.fsm.n_engine_runs                         = 1;

  // Custom registers
  wrapper->ctrl.custom_regs.n_total_reqs                  = n_total_reqs;
  wrapper->ctrl.custom_regs.t_ck_reqs                     = t_ck_reqs;
  wrapper->ctrl.custom_regs.t_ck_idle                     = t_ck_idle; 
}

void arov_map_params_traffic_gen(
  // Accelerator-rich overlay
  AROV_DEVICE_PTR arov, 
  // System parameters
  const int cluster_id, 
  const int accelerator_id,
  // L1 accelerator buffer
  DEVICE_PTR_CONST l1_arov_acc_buffer,
  uint32_t dim_traffic_gen_buffers,
  // Workload paramaters
  uint32_t width, 
  uint32_t height, 
  uint32_t stripe_height,
  uint32_t n_total_reqs, 
  uint32_t t_ck_reqs, 
  uint32_t t_ck_idle, 
  uint32_t max_buffer_dim,
  uint32_t n_reps,
  uint32_t n_tcdm_banks) { 

  /* Define parameters */

  hwpe_traffic_gen_workload_params params;

  params.standard.width            = width;
  params.standard.height           = height;
  params.standard.stripe_height    = stripe_height;
  params.standard.stim_dim         = width * height;
  params.standard.stripe_length    = width * stripe_height;
  params.standard.buffer_dim       = width * height;

  params.standard.buffer_stride    = 0;    
  params.standard.data_stride      = 1;  

  params.n_total_reqs     = n_total_reqs; 
  params.t_ck_reqs        = t_ck_reqs; 
  params.t_ck_idle        = t_ck_idle;
  params.max_buffer_dim   = max_buffer_dim;
  params.n_reps           = n_reps;
  params.n_tcdm_banks     = n_tcdm_banks;

  /* L1 buffer pointer */

  hwpe_l1_ptr_struct l1_traffic_gen_buffer;

  l1_traffic_gen_buffer.ptr = (DEVICE_PTR_CONST)l1_arov_acc_buffer + dim_traffic_gen_buffers * accelerator_id;

  /* Decide which hardware accelerator to program */

  if(cluster_id == 0){
    switch (accelerator_id){

      case 0: traffic_gen_wrapper_map_params(&(arov->traffic_gen_0_0), &l1_traffic_gen_buffer, &params); break;
      case 1: traffic_gen_wrapper_map_params(&(arov->traffic_gen_0_1), &l1_traffic_gen_buffer, &params); break;
      case 2: traffic_gen_wrapper_map_params(&(arov->traffic_gen_0_2), &l1_traffic_gen_buffer, &params); break;
      case 3: traffic_gen_wrapper_map_params(&(arov->traffic_gen_0_3), &l1_traffic_gen_buffer, &params); break;
      default: printf("Error: No matching case for <arov_map_params_traffic_gen>\n"); break;
    }
  }
};
