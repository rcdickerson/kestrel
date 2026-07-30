#[no_mangle]
pub fn right(a: &mut [i32; 11]) {
    let n = 10;
    let mut j = 0;
    let mut max = 0;
    let mut maxi = 0;

    while j < n {
        if j == 0 {
            max = a[0];
            maxi = 0;
        }
        if max < a[j] {
            max = a[j];
            maxi = j;
        }
        if j == n {
            let t = a[n];
            a[n] = max;
            a[maxi] = t;
        }
        j = j + 1;
    }
}