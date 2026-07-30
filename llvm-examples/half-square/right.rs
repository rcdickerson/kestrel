#[no_mangle]
pub fn right(low: i32, h: i32) {
    let mut i = 0;
    let mut y = 0;
    let mut v = 0;
    while h > i {
        i = i + 1;
        y = y + y;
    }
    v = 1;
    while low > i {
        i = i + 1;
        y = y + y;
    }
}
