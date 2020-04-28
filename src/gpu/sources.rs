use ff_cl_gen as ffgen;
use paired::Engine;

// Instead of having a very large OpenCL program written for a specific curve, with a lot of
// rudandant codes (As OpenCL doesn't have generic types or templates), this module will dynamically
// generate OpenCL codes given different PrimeFields and curves.

static FFT_SRC: &str = include_str!("fft/fft.cl");
static FIELD2_SRC: &str = include_str!("multiexp/field2.cl");
static EC_SRC: &str = include_str!("multiexp/ec.cl");
static MULTIEXP_SRC: &str = include_str!("multiexp/multiexp.cl");

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
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        ffgen::field::<E::Fr>("Fr"),
        fft("Fr"),
        ffgen::field::<E::Fq>("Fq"),
        ec("Fq", "G1"),
        multiexp("G1", "Fr"),
        field2("Fq2", "Fq"),
        ec("Fq2", "G2"),
        multiexp("G2", "Fr")
    ));
}
