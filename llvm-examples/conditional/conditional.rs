pub fn get_discount(age: i32) -> i32 {
    if age >= 65 {
        20
    } else if age <= 12 {
        50
    } else {
        0
    }
}