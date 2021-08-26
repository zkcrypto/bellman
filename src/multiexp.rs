use super::multicore::Worker;
use ff::{FieldBits, PrimeFieldBits};
use futures::Future;
use group::prime::PrimeCurve;
use std::sync::Arc;

use super::SynthesisError;

fn multiexp_inner<D, G>(
    pool: &Worker,
    density_map: D,
    exponents: Arc<Vec<FieldBits<<G::Scalar as PrimeFieldBits>::ReprBits>>>,
) -> Box<dyn Future<Item = G, Error = SynthesisError>>
where
    D: Send + Sync + 'static + Clone + AsRef<bool>,
    G: PrimeCurve,
    G::Scalar: PrimeFieldBits,
{
    let exponents = exponents.clone();
    let density_map = density_map.clone();

    // Sort the bases into buckets
    for (exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
        // This if is required to reproduce.
        if density {
            let (exp_is_zero, exp_is_one) = {
                let (first, rest) = exp.split_first().unwrap();
                (!*first, *first)
            };
        }
    }
}
