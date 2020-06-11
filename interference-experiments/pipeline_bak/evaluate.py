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

#bms = ["2mm", "3mm", "atax", "axpy", "bicg", "conv2d", "gemm", "seq"]
bms = ["2mm", "3mm", "axpy", "bicg", "conv2d", "seq"]
#bms = ["axpy", "bicg", "conv2d", "seq"]
setting = ["noPREM", "PREM"]
rows = 3
bins = 100
ext = ".pdf"
path = "measurements/"
log = False

'''
# Code for each fg program with each bg program
for bm in bms:
    fig, ax = plt.subplots(rows, int(len(bms)/rows))
    fig.tight_layout

    # Load data without interference
    noint = pd.read_csv(path+bm+"_noint.csv", header=None)

    # Evaluate with interference
    for cnt, bg in enumerate(bms):

        # Load data with interference
        noprem = pd.read_csv(path+bm+"_"+bg+"_noPREM.csv", header=None)
        prem = pd.read_csv(path+bm+"_"+bg+"_PREM.csv", header=None)

        # Plot with noPREM interference
        smallest = min(noint.min().iloc[0], noprem.min().iloc[0], prem.min().iloc[0])
        biggest = max(noint.max().iloc[0], noprem.max().iloc[0], prem.max().iloc[0])

       # Plot without interference
        print(int(cnt/(len(bms)/rows)), int(cnt%(len(bms)/rows)))
        cur = ax[int(cnt/(len(bms)/rows)), int(cnt%(len(bms)/rows))]
        noint.hist(ax=cur, bins=bins, label="no interference", range=(smallest, biggest), log=log)
        noprem.hist(ax=cur, bins=bins, label="noPREM", range=(smallest, biggest), log=log)
        prem.hist(ax=cur, bins=bins, label="PREM", range=(smallest, biggest), log=log)

        # Label the subplot
        cur.legend()
        cur.set_title(bg, fontsize=5)

    fig.suptitle(bm)
    fig.subplots_adjust(hspace=0.4, wspace=0.2)
    fig.savefig(bm+"_eval"+ext)

'''

# Code for each fg program with seq as bg program
cnt = 0
fig, ax = plt.subplots(rows, int(len(bms)/rows))
fig.tight_layout

# Print table with benchmark,
print(",\gls{bcet},,,,\gls{acet},,,,\gls{wcet},,,,Jitter")
print("seq_bg,\
,no interference,no\gls{prem},\gls{prem},\
,no interference,no\gls{prem},\gls{prem},\
,no interference,no\gls{prem},\gls{prem},\
,no interference,no\gls{prem},\gls{prem}")

for bm in bms:

    # Load data without interference
    noint = pd.read_csv(path+bm+"_noint.csv", header=None)

    # Load data with interference
    noprem = pd.read_csv(path+bm+"_seq_noPREM.csv", header=None)
    prem = pd.read_csv(path+bm+"_seq_PREM.csv", header=None)

    # Plot with noPREM interference
    smallest = min(mymin(noint), mymin(noprem), mymin(prem))
    biggest = max(mymax(noint), mymax(noprem), mymax(prem))

    # Print WCET and Jitter
    commaprint([bm,"",round(mymin(noint),4),round(mymin(noprem),4),round(mymin(prem),4),"",
                      round(myavg(noint),4),round(myavg(noprem),4),round(myavg(prem),4),"",
                      round(mymax(noint),4),round(mymax(noprem),4),round(mymax(prem),4),"",
                      round(jittr(noint),4),round(jittr(noprem),4),round(jittr(prem),4)])

    # Plot without interference
    cur = ax[int(cnt/(len(bms)/rows)), int(cnt%(len(bms)/rows))]
    noint.hist(ax=cur, bins=bins, label="no interference", range=(smallest, biggest), log=log)
    noprem.hist(ax=cur, bins=bins, label="noPREM", range=(smallest, biggest), log=log)
    prem.hist(ax=cur, bins=bins, label="PREM", range=(smallest, biggest), log=log)

    # Label the subplot
    cur.legend()
    cur.set_title(bm, fontsize=5)
    cnt += 1

fig.subplots_adjust(hspace=0.4, wspace=0.2)
fig.savefig("seq_bg_eval"+ext)


