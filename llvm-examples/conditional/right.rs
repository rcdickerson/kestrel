#[no_mangle] pub fn right(age: i32){
    let mut ret_val = 0;
    if age >= 65 {
        ret_val = 20;
    } else if age <= 12 {
        ret_val = 50;
    } 
}