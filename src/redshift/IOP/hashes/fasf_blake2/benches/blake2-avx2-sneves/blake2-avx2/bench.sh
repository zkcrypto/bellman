for primitive in blake2b.c blake2bp.c blake2sp.c
do
  for compiler in gcc clang
  do
    for opt in -O3 -Os
    do
      for impl in PERMUTE_WITH_NONE PERMUTE_WITH_SHUFFLES PERMUTE_WITH_GATHER
      do
        $compiler $opt -D$impl -DSUPERCOP -std=gnu99 -mavx2 -o bench.exe bench.c $primitive
        echo $compiler $opt -D$impl $primitive
        taskset -c 0 ./bench.exe | tail -3
        rm -f bench.exe
      done
    done
  done
done
