use vergen::{generate_cargo_keys, ConstantsFlags};

fn main() {
    let flags = ConstantsFlags::BUILD_DATE
        | ConstantsFlags::SHA_SHORT
        | ConstantsFlags::REBUILD_ON_HEAD_CHANGE;
    generate_cargo_keys(flags).expect("Unable to generate the cargo keys!");
}
