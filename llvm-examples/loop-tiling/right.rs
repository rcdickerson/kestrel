pub fn f(x: i32) -> i32 { x }

#[no_mangle]
pub fn right(a: &mut [[i32; 10]; 10]) {
    let n = 10;
    let m = 10;
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < m {
            a[i][j] = f((i * n + j) as i32);
            j = j + 1;
        }
        i = i + 1;
    }
}