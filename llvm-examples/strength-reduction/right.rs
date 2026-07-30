#[no_mangle]
pub fn right(B: i32, C: i32, N: i32, mut x: i32) {
    let mut i = 0;
    let mut j = C;
    while i < N {
        x = x + j;
        j = j + B;
        i = i + 1;
    }
}
