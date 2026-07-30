#[no_mangle]
pub fn right(a: &mut [i32; 21], b: &mut [i32; 21]) {
    let n = 20;
    let mut j = 1;
    let mut d = [0; 21];

    d[1] = b[0];
    while j <= n - 1 {
        b[j] = a[j];
        d[j + 1] = b[j];
        j = j + 1;
    }
    b[n] = a[n];
}