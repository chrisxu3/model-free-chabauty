from lmf import db

levels = [10,12,14,15,18,20,21,22,24,26,28,30,36,40,42,44,48,50,52,54,56,60]
levels_higher = [72,78,84,88,100,104,108,120,168,200,216]

for N in levels:
    db.mf_newforms.search()