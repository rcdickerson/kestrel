#[no_mangle]
pub fn right(x: i32) {
    let mut z = 2 * x;
    let mut y = 0;
    while z > 0 {
        z = z - 1;
        y = y + x;
    }
}