#[no_mangle]
pub fn right(a: &mut [i32; 10], b: &mut [i32; 10], c: &mut [i32; 10]) {
    let n = 10;
    let mut j = 0;

    a[0] = a[0] + 1;
    b[0] = b[0] + a[0];
    a[1] = a[1] + 1;

    while j < n - 2 {
        a[j + 2] = a[j + 2] + 1;
        b[j + 1] = b[j + 1] + a[j + 1];
        c[j] = c[j] + b[j];
        j = j + 1;
    }

    c[j] = c[j] + b[j];
    b[j + 1] = b[j + 1] + a[j + 1];
    c[j + 1] = c[j + 1] + b[j + 1];
}
