//! What Soma's add.definition describes: functions of whole numbers,
//! exported by name. WebAssembly has no unsigned 64-bit type of its own, so
//! these take and return i64, and add wraps around past i64::MAX, as
//! machine addition does: add.definition says what Soma takes them to be,
//! and Soma checks it on every call.

/// a + b, wrapping around past i64::MAX
#[no_mangle]
pub extern "C" fn add(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}

/// the n-th Fibonacci number, by repeated addition
#[no_mangle]
pub extern "C" fn fib(n: i64) -> i64 {
    let (mut a, mut b) = (0i64, 1i64);
    for _ in 0..n {
        let next = add(a, b);
        a = b;
        b = next;
    }
    a
}

/// the length of the hypotenuse of a right triangle with sides a and b
#[no_mangle]
pub extern "C" fn hypot(a: f64, b: f64) -> f64 {
    (a * a + b * b).sqrt()
}

/// x / 2, in single precision
#[no_mangle]
pub extern "C" fn half(x: f32) -> f32 {
    x / 2.0
}
