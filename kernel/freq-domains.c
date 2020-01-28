/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include <pulp.h>


int pos_freq_domains[ARCHI_NB_FLL];



int pos_freq_set_and_get(pi_freq_domain_e domain, unsigned int freq, unsigned int *out_freq)
{
    int irq = hal_irq_disable();

    int fll_freq = pos_fll_set_freq(pos_freq_get_fll(domain), freq);
    if (out_freq)
      *out_freq = fll_freq;

    pos_freq_domains[domain] = freq;

    hal_irq_restore(irq);

    return 0;
}


