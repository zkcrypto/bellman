use crate::multicore::*;
use crate::pairing::ff::PrimeField;

pub(crate) fn convert_to_field_elements<F: PrimeField>(indexes: &[usize], worker: &Worker) -> Vec<F> {
    let mut result = vec![F::zero(); indexes.len()];
    
    worker.scope(indexes.len(), |scope, chunk| {
        for (idx, fe) in indexes.chunks(chunk)
                .zip(result.chunks_mut(chunk)) {
            scope.spawn(move |_| {
                let mut repr = F::zero().into_repr();
                for (idx, fe) in idx.iter().zip(fe.iter_mut()) {
                    repr.as_mut()[0] = *idx as u64;
                    *fe = F::from_repr(repr).expect("is a valid representation");
                }
            });
        }
    });

    result
}

