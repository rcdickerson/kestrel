#[no_mangle]
pub fn right(mut a: i32, b: i32) {
    let mut c = 0;
    while a < b {
        c = c + (a * a);
        a = a + 1;
    }
}
