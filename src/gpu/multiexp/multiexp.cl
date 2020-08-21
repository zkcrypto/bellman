/*
 * Same multiexp algorithm used in Bellman, with some modifications.
 * https://github.com/zkcrypto/bellman/blob/10c5010fd9c2ca69442dc9775ea271e286e776d8/src/multiexp.rs#L174
 * The CPU version of multiexp parallelism is done by dividing the exponent
 * values into smaller windows, and then applying a sequence of rounds to each
 * window. The GPU kernel not only assigns a thread to each window but also
 * divides the bases into several groups which highly increases the number of
 * threads running in parallel for calculating a multiexp instance.
 */

__kernel void POINT_bellman_multiexp(
    __global POINT_affine *bases,
    __global POINT_projective *buckets,
    __global POINT_projective *results,
    __global EXPONENT *exps,
    uint n,
    uint num_groups,
    uint num_windows,
    uint window_size) {

  // We have `num_windows` * `num_groups` threads per multiexp.
  const uint gid = get_global_id(0);
  if(gid >= num_windows * num_groups) return;

  // We have (2^window_size - 1) buckets.
  const uint bucket_len = ((1 << window_size) - 1);

  // Each thread has its own set of buckets in global memory.
  buckets += bucket_len * gid;

  const POINT_projective local_zero = POINT_ZERO;
  for(uint i = 0; i < bucket_len; i++) buckets[i] = local_zero;

  const uint len = (uint)ceil(n / (float)num_groups); // Num of elements in each group

  // This thread runs the multiexp algorithm on elements from `nstart` to `nened`
  // on the window [`bits`, `bits` + `w`)
  const uint nstart = len * (gid / num_windows);
  const uint nend = min(nstart + len, n);
  const uint bits = (gid % num_windows) * window_size;
  const ushort w = min((ushort)window_size, (ushort)(EXPONENT_BITS - bits));

  POINT_projective res = POINT_ZERO;
  for(uint i = nstart; i < nend; i++) {
    uint ind = EXPONENT_get_bits(exps[i], bits, w);

    #ifdef NVIDIA
      // O_o, weird optimization, having a single special case makes it
      // tremendously faster!
      // 511 is chosen because it's half of the maximum bucket len, but
      // any other number works... Bigger indices seems to be better...
      if(ind == 511) buckets[510] = POINT_add_mixed(buckets[510], bases[i]);
      else if(ind--) buckets[ind] = POINT_add_mixed(buckets[ind], bases[i]);
    #else
      if(ind--) buckets[ind] = POINT_add_mixed(buckets[ind], bases[i]);
    #endif
  }

  // Summation by parts
  // e.g. 3a + 2b + 1c = a +
  //                    (a) + b +
  //                    ((a) + b) + c
  POINT_projective acc = POINT_ZERO;
  for(int j = bucket_len - 1; j >= 0; j--) {
    acc = POINT_add(acc, buckets[j]);
    res = POINT_add(res, acc);
  }

  results[gid] = res;
}
