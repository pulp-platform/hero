#!/bin/python3

import sys
import pickle
import pandas as pd
import numpy as np

################
size = '2048KB'
run_path = './'
################

# Load results
with open(run_path+'tensor.pkl', 'rb') as f:
	tensor = pickle.load(f)

with open(run_path+'labels.pkl', 'rb') as f:
	labels  = pickle.load(f)

memory = labels[0]
fg = labels[1]
bg = labels[2]

if False:
	data = tensor[memory.index(size), :, bg.index('seq'), :]
	progs, meas = data.shape
	thresholds = [0, 0, 0.05, 0.02, 0.04, 0.02, 0.1, 0.03]
	counts = np.zeros(progs)
	for i in range(meas):
		for prog in range(progs):
			if data[prog, i] > thresholds[prog]:
				counts[prog] +=1 

	print(fg)
	print(counts)

# Generate dataframes for no interference and seq interfering
size_index = memory.index(size)
seq_index = bg.index('seq')

df_min_none = pd.DataFrame(tensor[size_index, :, 0, :].min(axis=1).T, index=fg)
df_avg_none = pd.DataFrame(tensor[size_index, :, 0, :].mean(axis=1).T, index=fg)
df_max_none = pd.DataFrame(tensor[size_index, :, 0, :].max(axis=1).T, index=fg)
#df_max_none = pd.DataFrame(np.sort(tensor[size_index, :, 0, :])[:, -10].T, index=fg)

df_min_seq = pd.DataFrame(tensor[size_index, :, seq_index, :].min(axis=1).T, index=fg)
df_avg_seq = pd.DataFrame(tensor[size_index, :, seq_index, :].mean(axis=1).T, index=fg)
df_max_seq = pd.DataFrame(tensor[size_index, :, seq_index, :].max(axis=1).T, index=fg)
#df_max_seq = pd.DataFrame(np.sort(tensor[size_index, :, seq_index, :])[:, -10].T, index=fg)

# Compute ACET and WCET
df_avg = pd.concat([df_avg_none*1000, df_avg_seq*1000, df_avg_seq/df_avg_none], axis=1)
df_avg.columns = ['ACET isolated[ms]', 'ACET with seq [ms]', 'ACET factor']

df_max = pd.concat([df_max_none*1000, df_max_seq*1000, df_max_seq/df_max_none], axis=1)
df_max.columns = ['WCET isolated [ms]', 'WCET with seq [ms]', 'WCET factor']

print(df_avg)
print(df_max)

# Compute overlap
df_minmin = pd.concat([df_min_none, df_min_seq], axis=1).min(axis=1)
df_maxmin = pd.concat([df_min_none, df_min_seq], axis=1).max(axis=1)
df_minmax= pd.concat([df_max_none, df_max_seq], axis=1).min(axis=1)
df_maxmax= pd.concat([df_max_none, df_max_seq], axis=1).max(axis=1)

df_temp = pd.concat([100*(df_minmax-df_maxmin)/(df_maxmax-df_minmin), pd.DataFrame(np.zeros(len(fg)), index=fg)], axis=1)
df_overlap = pd.concat([df_minmin, df_maxmin, df_minmax, df_maxmax, df_temp.max(axis=1)], axis=1)
df_overlap.columns = ['minmin', 'maxmin', 'minmax', 'maxmax', 'Overlap [%]']
print(df_overlap)

# Compute jitter
df_jit_none = pd.concat([df_avg_none-df_min_none, df_max_none-df_avg_none], axis=1).max(axis=1)
df_jit_seq = pd.concat([df_avg_seq-df_min_seq, df_max_seq- df_avg_seq], axis=1).max(axis=1)

df_jitter = pd.concat([df_jit_none*1000, df_jit_seq*1000, df_jit_seq/df_jit_none], axis=1)
df_jitter.columns = ['Jitter isolated [ms]', 'Jitter with seq [ms]', 'Jitter factor']
print(df_jitter)

# Combine all dataframes
norm = 2
df_total = pd.concat([df_avg.round(norm), df_max.round(norm), df_overlap['Overlap [%]'].round(3), df_jitter.round(norm)], axis=1).T
print(df_total)
print(df_total.to_latex())

