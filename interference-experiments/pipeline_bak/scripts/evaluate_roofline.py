import pandas as pd

# Setup parameters
size = 2048  
root = "/scratch/mmaxim/hero_bak/interference-experiments/pipeline"
K =  ['1', '2', '4' ,'8', '16', '32', '64']#, '128', '256', '512', '1024']
freq = ['50', '100', '150', '200', '225', '250', '300']
times  = pd.DataFrame(columns = K, index = freq)

# Extract measurements into dataframe
for f in freq:
	for k in K: 
		filename = root+"/data/seq_2048KB_"+k+"kernloops/2TG_at_"+f+"MHz.csv"
		temp = pd.read_csv(filename, header=None)
		times.loc[f, k] = temp.iloc[:128].median()[0]

# Compute stuff
stuff = pd.DataFrame(columns=K, index=["FLOPs", "FLOP/Byte"])
single = size*1024/2/4
bytes_loaded = size*1024

for k in K:
	flop = single*int(k)
	stuff.loc["FLOPs", k]= flop
	stuff.loc["FLOP/Byte", k] = flop/bytes_loaded

# Generate resulting dataframe
res = 1/times
res = res.mul(stuff.loc["FLOPs"])/1E9
res.columns = stuff.loc["FLOP/Byte"]
res.index = res.index+" MHz"

bw = []
for f in freq:
	bw.append(", 2TG, "+str(round(int(f)*2*128/8/19200*100))+"% BW")

res.index = res.index+bw

ax = res.T.plot(logx=True, linestyle="--")
ax.set(title="Roofline (2TG, median of 128 measurements)", ylabel="GLoopIter/s")
fig = ax.get_figure()
fig.savefig("roofline.pdf")
