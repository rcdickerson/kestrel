#[no_mangle] pub fn sum_to_n(n: i32) -> i32{
    let mut sum = 0;
    let mut i = 1;
    while i <= n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}