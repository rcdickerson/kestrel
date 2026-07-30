#[no_mangle]
pub fn right(x: i32) {
    let mut y = x;
    let mut z = 16;
    let mut w = 0;
    
    while y > 4 {
        if w % 3 == 0 {
            z = z * 2;
            y = y - 1;
        }
        w = w + 1;
    }
}