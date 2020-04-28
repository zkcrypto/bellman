use ff::PrimeField;
use ff_cl_gen as ffgen;
use paired::Engine;

// Instead of having a very large OpenCL program written for a specific curve, with a lot of
// rudandant codes (As OpenCL doesn't have generic types or templates), this module will dynamically
// generate OpenCL codes given different PrimeFields and curves.

static FFT_SRC: &str = include_str!("fft/fft.cl");
static EXP_SRC: &str = include_str!("multiexp/exp.cl");
static FIELD2_SRC: &str = include_str!("multiexp/field2.cl");
static EC_SRC: &str = include_str!("multiexp/ec.cl");
static MULTIEXP_SRC: &str = include_str!("multiexp/multiexp.cl");

/// Divide anything into 64bit chunks
fn limbs_of<T>(value: &T) -> &[u64] {
    unsafe {
        std::slice::from_raw_parts(
            value as *const T as *const u64,
            std::mem::size_of::<T>() / 8,
        )
    }
}

fn exponent<F>(name: &str) -> String
where
    F: PrimeField,
{
    return format!(
        "{}\n{}\n",
        format!("#define {}_LIMBS {}", name, limbs_of(&F::one()).len()),
        String::from(EXP_SRC).replace("EXPONENT", name)
    );
}

fn field2(field2: &str, field: &str) -> String {
    return String::from(FIELD2_SRC)
        .replace("FIELD2", field2)
        .replace("FIELD", field);
}

fn fft(field: &str) -> String {
    return String::from(FFT_SRC).replace("FIELD", field);
}

fn ec(field: &str, point: &str) -> String {
    return String::from(EC_SRC)
        .replace("FIELD", field)
        .replace("POINT", point);
}

fn multiexp(point: &str, exp: &str) -> String {
    return String::from(MULTIEXP_SRC)
        .replace("POINT", point)
        .replace("EXPONENT", exp);
}

// WARNING: This function works only with Short Weierstrass Jacobian curves with Fq2 extension field.
pub fn kernel<E>() -> String
where
    E: Engine,
{
    return String::from(format!(
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        ffgen::common(),
        ffgen::field::<E::Fr>("Fr"),
        fft("Fr"),
        exponent::<E::Fr>("Exp"),
        ffgen::field::<E::Fq>("Fq"),
        ec("Fq", "G1"),
        multiexp("G1", "Exp"),
        field2("Fq2", "Fq"),
        ec("Fq2", "G2"),
        multiexp("G2", "Exp")
    ));
}
