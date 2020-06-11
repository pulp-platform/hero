import matplotlib.pyplot as plt
import pandas as pd
from matplotlib import rc

def mymax(df):
    return df.max().iloc[0]

def mymin(df):
    return df.min().iloc[0]

def myavg(df):
    return df.mean().iloc[0]

def jittr(df):
    return max(myavg(df)-mymin(df), mymax(df)-myavg(df))

def commaprint(list):
    string = ""
    for elem in list:
        string += str(elem) + ","

    print(string[:-1])


# Set fontsizes to fit inside a small space, increase img quality
rc('xtick', labelsize=3)
rc('ytick', labelsize=3)
rc('legend', fontsize=4)
rc('savefig', dpi=1000)
rc('savefig', jpeg_quality=100)

bins = 100
ext = ".pdf"
path = "measurements/"
log = False

fig, ax = plt.subplots(1)
fig.tight_layout

process = ["0", "1", "2", "3"]
cmux = ["0", "1", "2", "3"]
bench = ["0", "1", "2", "3"]
dflist = []
labels = []
windows = []

shortest=-1
longest=-1
for pc in process:
    for cc in cmux:
        if (cc != pc):
            for bc in bench:
                if ((cc != bc) and (pc != bc)):
                    label = "3mm-"+bc+"_proc-"+pc+"_cmux-"+cc
                    labels.append(label)
                    df = pd.read_csv(path+label )
                    dflist.append(df)
                    cur_max=mymax(df)
                    cur_min=mymin(df)
                    print(label,cur_max-cur_min, cur_max, cur_min)
                    windows.append(cur_max-cur_min)
                    if (cur_max > longest):
                        longest = cur_max
                    if ((shortest == -1) or (shortest > cur_min)):
                        shortest = cur_min

df=pd.concat(dflist)
df.boxplot(ax=ax, vert=False)

ax.set_title("3mm in Isolation")
fig.savefig("3mm_isolation"+ext)


