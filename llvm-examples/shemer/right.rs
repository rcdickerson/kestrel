#[no_mangle]
pub fn right(x: i32) {
    let mut y = 0;
    let z = x;
    let mut i = 0;
    
    while i < z {
        y = y + x;
        i = i + 1;
    }
    y = y * 2;
}