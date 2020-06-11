import pandas as pd

# Setup parameters
size = 2048  
root = "/home/mmaxim/polybox/PhD/polybench"
measure = "median"
samples = 1024 
tg_count = 4
#TG = ['1_1230', '2_0321', '2_0123', '3_0321', '3_0123', '4_1230']
#labels = ['1 TG on 1 Port', '2 TG on 1 Port', '2 TG on 2 Ports', '3 TG on 2 Ports', '3 TG on 3 Ports', '4 TG on 3 Ports']
if tg_count == 1:
	TG = [    '1_0321', '1_1230', '1_2130', '1_3120']
	labels = ['TG 0',   'TG 1',   'TG 2',   'TG 3']
	max_f = 300
elif tg_count == 2:
	TG = [    '2_0123', '2_0213', '2_0321', '2_1230', '2_3120', '2_3210']
	labels = ['TG 01',  'TG 02',  'TG 03',  'TG 12',  'TG 13',  'TG 23']
	max_f = 600 
elif tg_count == 3:
	TG = ['3_0123', '3_1230', '3_0321', '3_0132']
	labels = ['TG 012', 'TG 123', 'TG 023', 'TG 013']
	max_f = 700
elif tg_count == 4:
	TG = [    '4_0321']
	labels = ['TG 0123']
	max_f = 950

tot_freq = []
for f in range(50,max_f+50,50):
	tot_freq.append(str(f))
percentage = []
tot_bw=19200 # DRAM BW in MB/s

df = pd.DataFrame(columns=tot_freq, index=TG)


# Extract measurements into dataframe
for f in tot_freq:
	percentage.append(str(round(int(f)*128/8/tot_bw*100)))
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

print(df)

# Prepare dataframe to be plotted
df.columns = percentage

df.index = labels
df = df.sort_index(ascending=False)
print(df)

# Plot
ax = df.T.plot(linestyle='--')
ax.set(title=str(tg_count)+" TG Bandwidth Injection ("+measure+" of "+str(samples)+" measurements)", 
	ylabel="Execution Time [s]", 
#	yscale='log',
	xlabel="Injected BW [%]")
fig = ax.get_figure()
fig.subplots_adjust(left=0.15, bottom=0.15)
fig.savefig("injection"+str(tg_count)+".pdf")

