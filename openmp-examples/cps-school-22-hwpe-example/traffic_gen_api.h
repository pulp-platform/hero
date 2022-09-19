#ifndef __TRAFFIC_GEN_API_H__
#define __TRAFFIC_GEN_API_H__

/* System libraries. */
#include <hero-target.h>
#include <arov-target.h>


/* Struct */
typedef struct {
  uint32_t n_total_reqs; 
  uint32_t t_ck_reqs; 
  uint32_t t_ck_idle;
  uint32_t max_buffer_dim;
  uint32_t n_reps;
  uint32_t n_tcdm_banks;
  hwpe_dataset_params_struct standard;
} hwpe_traffic_gen_workload_params;

/* Definitions */

static inline void traffic_gen_wrapper_map_params(
  traffic_gen_wrapper_struct *wrapper, 
  hwpe_l1_ptr_struct *l1_buffer, 
  hwpe_traffic_gen_workload_params *params);

void arov_map_params_traffic_gen(
  // Accelerator-rich overlay
  AROV_DEVICE_PTR arov, 
  // System parameters
  const int cluster_id, 
  const int accelerator_id,
  // L1 accelerator buffer
  DEVICE_PTR_CONST l1_traffic_gen_buffer,
  uint32_t dim_traffic_gen_buffer,
  // Workload paramaters
  uint32_t width, 
  uint32_t height, 
  uint32_t stripe_height,
  uint32_t n_total_reqs, 
  uint32_t t_ck_reqs, 
  uint32_t t_ck_idle, 
  uint32_t max_buffer_dim,
  uint32_t n_reps,
  uint32_t n_tcdm_banks);

#endif