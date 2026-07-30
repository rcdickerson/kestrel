#[no_mangle]
pub fn right(a: &mut [f32; 10]) {
    let n = 10;
    let mut i = 0;
    while i < n {
        let mut j = n - 1;
        while j > i {
            if a[j - 1] > a[j] {
                let temp = a[j];
                a[j] = a[j - 1];
                a[j - 1] = temp;
            }
            j = j - 1;
        }
        i = i + 1;
    }
}