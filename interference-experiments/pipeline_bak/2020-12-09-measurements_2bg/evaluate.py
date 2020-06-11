import matplotlib.pyplot as plt
import pandas as pd
from matplotlib import rc

# Set fontsizes to fit inside a small space, increase img quality
rc('xtick', labelsize=3)
rc('ytick', labelsize=3)
rc('legend', fontsize=4)
rc('savefig', dpi=1000)
rc('savefig', jpeg_quality=100)

bms = ["2mm", "3mm", "atax", "axpy", "bicg", "conv2d", "gemm", "seq"]
#bms = ["axpy", "bicg", "conv2d", "seq"]
setting = ["noPREM", "PREM"]
rows = 4
bins = 100
ext = ".png"
path = "measurements/"
log = False

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


# Code for each fg program with seq as bg program
cnt = 0
fig, ax = plt.subplots(rows, int(len(bms)/rows))
fig.tight_layout

for bm in bms:

    # Load data without interference
    noint = pd.read_csv(path+bm+"_noint.csv", header=None)

    # Load data with interference
    noprem = pd.read_csv(path+bm+"_seq_noPREM.csv", header=None)
    prem = pd.read_csv(path+bm+"_seq_PREM.csv", header=None)

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
    cur.set_title(bm, fontsize=5)
    cnt += 1

fig.suptitle("seq background")
fig.subplots_adjust(hspace=0.4, wspace=0.2)
fig.savefig("seq_bg_eval"+ext)


