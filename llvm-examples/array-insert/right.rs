#[no_mangle]
pub fn right(a: &mut [i32; 11], val: i32) {
    let a_size = 10;
    let mut j = 0;

    while j < a_size && a[j] < val {
        j = j + 1;
    }

    let len = a_size + 1;
    a[j] = val;

    while j < len {
        j = j + 1;
    }
}