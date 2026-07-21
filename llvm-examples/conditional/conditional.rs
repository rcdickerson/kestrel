#[no_mangle] pub fn get_discount(age: i32) -> i32{
    let mut ret_val = 0;
    if age >= 65 {
        ret_val = 20;
    } else if age <= 12 {
        ret_val = 50;
    } 
    ret_val
}