//! A module that Soma uses without a .definition: its exports are of type
//! Any to Soma, and what it gives back is the number it is, an integer (Z).

/// a * b, wrapping around past i64::MAX
#[no_mangle]
pub extern "C" fn mul(a: i64, b: i64) -> i64 {
    a.wrapping_mul(b)
}
