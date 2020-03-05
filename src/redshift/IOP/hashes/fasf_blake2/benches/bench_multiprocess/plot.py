#! /usr/bin/python3

import matplotlib.pyplot as plt
import sys

filename = sys.argv[1]

xs = []
ys = []
for line in open(filename):
    (x, y) = line.split()
    xs.append(int(x))
    ys.append(float(y))

# plt.plot(xs, ys, marker=".", linestyle="none")
plt.plot(xs, ys, marker=".")
plt.xlabel("byte offset of input from a page boundary")
plt.ylabel("throughput (GB/s)")
plt.title(filename)
plt.show()
