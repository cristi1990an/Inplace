use inplace_containers::*;

fn main() {
    let str = inplace_string!("test");
    let vec = inplace_vec!(7;
        "1".to_owned(),
        "2".to_owned(),
        "3".to_owned(),
        "4".to_owned());

    println!("{str:?}");
    println!("{vec:?}");
}
