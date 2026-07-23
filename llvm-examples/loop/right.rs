#[no_mangle] pub fn right(n: i32){
    let mut sum = 0;
    let mut i = 1;
    while (i <= n) {
        sum = sum + i;
        i = i + 1;
    }
}