#[no_mangle]
pub fn right(a: &mut [i32; 10], b: &mut [i32; 10], c: &mut [i32; 10], k: i32, x: i32) {
    let n = 10;
    if x < 7 {
        let mut j = 0;
        while j < n {
            a[j] = a[j] + k;
            b[j] = a[j] * c[j];
            j = j + 1;
        }
    } else {
        let mut j = 0;
        while j < n {
            a[j] = a[j] + k;
            b[j] = a[j - 1] * b[j - 1];
            j = j + 1;
        }
    }
}
