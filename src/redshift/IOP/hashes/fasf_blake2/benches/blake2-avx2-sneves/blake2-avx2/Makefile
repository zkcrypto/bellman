CFLAGS=-std=c89 -Ofast -march=haswell -Wall -Wextra -pedantic -Wfatal-errors -Wno-long-long

all: check

bench: check
	$(SHELL) bench.sh

check: blake2b-check-1.exe blake2b-check-2.exe blake2b-check-3.exe blake2bp-check-1.exe blake2bp-check-2.exe blake2bp-check-3.exe blake2sp-check-1.exe blake2sp-check-2.exe blake2sp-check-3.exe

blake2b-check-1.exe: blake2b.c
	$(CC) $(CFLAGS) -DBLAKE2B_SELFTEST -DPERMUTE_WITH_NOTHING -o $@ $<
	./$@

blake2b-check-2.exe: blake2b.c
	$(CC) $(CFLAGS) -DBLAKE2B_SELFTEST -DPERMUTE_WITH_SHUFFLES -o $@ $<
	./$@

blake2b-check-3.exe: blake2b.c
	$(CC) $(CFLAGS) -DBLAKE2B_SELFTEST -DPERMUTE_WITH_GATHER -o $@ $<
	./$@

blake2bp-check-1.exe: blake2bp.c
	$(CC) $(CFLAGS) -DBLAKE2BP_SELFTEST -DPERMUTE_WITH_NOTHING -o $@ $<
	./$@

blake2bp-check-2.exe: blake2bp.c
	$(CC) $(CFLAGS) -DBLAKE2BP_SELFTEST -DPERMUTE_WITH_SHUFFLES -o $@ $<
	./$@

blake2bp-check-3.exe: blake2bp.c
	$(CC) $(CFLAGS) -DBLAKE2BP_SELFTEST -DPERMUTE_WITH_GATHER -o $@ $<
	./$@


blake2sp-check-1.exe: blake2sp.c
	$(CC) $(CFLAGS) -DBLAKE2SP_SELFTEST -DPERMUTE_WITH_NOTHING -o $@ $<
	./$@

blake2sp-check-2.exe: blake2sp.c
	$(CC) $(CFLAGS) -DBLAKE2SP_SELFTEST -DPERMUTE_WITH_SHUFFLES -o $@ $<
	./$@

blake2sp-check-3.exe: blake2sp.c
	$(CC) $(CFLAGS) -DBLAKE2SP_SELFTEST -DPERMUTE_WITH_GATHER -o $@ $<
	./$@

clean:
	rm -f *.exe