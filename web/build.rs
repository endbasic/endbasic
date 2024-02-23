use vergen::EmitBuilder;

fn main() {
    EmitBuilder::builder()
        .build_date()
        .git_sha(true)
        .emit()
        .expect("Unable to generate the cargo keys!");
}
