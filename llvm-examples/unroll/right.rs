#[no_mangle]
pub fn right(N: i32) {
    let mut x = 0;
    let mut i = 1;
    while i <= N {
        x = x + i;
        i = i + 1;
    }
}
