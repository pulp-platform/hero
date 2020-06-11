import pandas as pd
import numpy as np
from matplotlib import rc
rc('figure', figsize=(4.7, 3))

def sigmoid(arg):
	return 1/(1 + np.exp(-arg))

# Setup parameters
size = 2048
root = "/scratch/mmaxim/hero_bak/interference-experiments/pipeline"
measure = "median"
samples = 1024
TG = ['1_0123', '2_0123', '3_0123']
labels = ['1 TG', '2 TG', '3 TG']

max_f = 700
tot_freq = []

for f in range(50,max_f+50,50):
	tot_freq.append(str(f))

#percentage = []
#available = []
concurrent = []
tot_bw=19200 # DRAM BW in MB/s

df = pd.DataFrame(columns=tot_freq, index=TG)

# Extract measurements into dataframe
for f in tot_freq:
    #percentage.append(str(round(int(f)*128/8/tot_bw*100)))
    #available.append(str(round((tot_bw-int(f)*128/8)/tot_bw*100)))
    concurrent.append(int(f)*128/8*1000000)
    for g in TG:
        cur_g = int(g[0])
        filename = root+"/data/seq_2048KB_1kernloops/"+g+"_at_"+str(int(int(f)/cur_g))+"MHz.csv"
        try:
            temp = pd.read_csv(filename, header=None)
            if measure == "min":
                df.loc[g, f]=temp[:samples].min()[0]
            elif measure == "mean":
                df.loc[g, f]=temp[:samples].mean()[0]
            elif measure == "median":
                df.loc[g, f]=temp[:samples].median()[0]
            elif measure == "max":
                df.loc[g, f]=temp[:samples].max()[0]

        except FileNotFoundError:
            print("Did not find" + filename)
            continue

# Prepare dataframe to be plotted
df.columns = concurrent

df.index = labels
df = df.sort_index(ascending=False)
# Execution/s * iter/execution * ops/iter to get performance in [ops/s]
df = 1/df*262144*10.5


# Plot
ax = df.T.plot(linestyle='--')
ax.set(title="DRAM Straining", #("+measure+" of "+str(samples)+" runs)",
	ylabel="Performance [op/s]",
#	yscale='log',
	xlabel="Concurrent BW [B/s]")

# Prepare model and plot
y = []
a = 75
b = 65e6
c = 415000
P = df.max(axis=1)[0]
for x in concurrent:
    print(x/tot_bw)
    y.append(P-(a*x/tot_bw+b*sigmoid(x/tot_bw-c)))
#y = P - x
#y = (1/((1+x*0.035+sigmoid(5*(x-9))*1.1)))*df.max()[0]
ax.plot(concurrent, y, label='Model')
ax.legend(['3 TG', '2 TG', '1 TG', 'Model'])

# Save plot
fig = ax.get_figure()
#fig.subplots_adjust(left=0.15, bottom=0.15)
fig.savefig("injection.pdf")

