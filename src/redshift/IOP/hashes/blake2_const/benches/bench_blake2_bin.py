#! /usr/bin/env python3

from pathlib import Path
import subprocess
import os
import statistics
import tempfile
import time

# On my i5-8250U laptop, at 1MB of input or below, the results of the benchmark
# are pretty random. Above 10MB, all of the implementations keep getting
# faster, but their relative performance is consistent.
INPUT_SIZE = 1_000_000_000
NUM_RUNS = 10

bin_root = Path(__file__).parent / "../blake2_bin"
bin_path = str(bin_root / "target/release/blake2")

targets = [
    ["md5sum"],
    ["sha1sum"],
    ["sha512sum"],
    ["/usr/bin/b2sum"],
    [bin_path, "-b"],
    [bin_path, "-s"],
    [bin_path, "-bp"],
    [bin_path, "-sp"],
]


def print_diff(diff, gigs, message, stdev=None, stdev_rate=None):
    gb_per_sec = gigs / diff
    diff_stdev = ""
    gbps_stdev = ""
    if stdev is not None:
        diff_stdev = " ± {:.6f}".format(stdev)
    if stdev_rate is not None:
        gbps_stdev = " ± {:.6f}".format(stdev_rate)
    print("{:.6f}{} ({:.6f}{} GB/s)  {}".format(diff, diff_stdev, gb_per_sec,
                                                gbps_stdev, message))


def random_temp_file(size):
    f = tempfile.TemporaryFile()
    # Write random data 1 MiB at a time.
    while size > 2**20:
        f.write(os.urandom(2**20))
        size -= 2**20
    f.write(os.urandom(size))
    f.seek(0)
    return f


def main():
    input_file = random_temp_file(INPUT_SIZE)
    input_gigs = INPUT_SIZE / 1_000_000_000
    build_command = ["cargo", "build", "--release"]
    print(" ".join(build_command))
    subprocess.run(build_command, cwd=bin_root)

    averages = {}
    bests = {}
    stdevs = {}
    stdevs_rate = {}
    for target in targets:
        target_name = " ".join(target)
        runs = []
        rates = []
        best = float('inf')
        for i in range(NUM_RUNS):
            input_file.seek(0)

            # Do a run!
            start = time.perf_counter()
            subprocess.run(target, stdin=input_file, stdout=subprocess.DEVNULL)
            diff = time.perf_counter() - start

            if i == 0:
                print_diff(diff, input_gigs, target_name + " (ignored)")
            else:
                print_diff(diff, input_gigs, target_name)
                runs.append(diff)
                rates.append(input_gigs / diff)
        averages[target_name] = sum(runs) / len(runs)
        bests[target_name] = min(runs)
        stdevs[target_name] = statistics.stdev(runs)
        stdevs_rate[target_name] = statistics.stdev(rates)

    print("--- best ---")
    best_list = list(bests.items())
    best_list.sort(key=lambda pair: pair[1])
    for target_name, best in best_list:
        print_diff(best, input_gigs, target_name)

    print("--- average ---")
    average_list = list(averages.items())
    average_list.sort(key=lambda pair: pair[1])
    for target_name, average in average_list:
        print_diff(
            average,
            input_gigs,
            target_name,
            stdev=stdevs[target_name],
            stdev_rate=stdevs_rate[target_name])


if __name__ == "__main__":
    main()
