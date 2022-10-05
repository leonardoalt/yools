use std::env;
use std::fs::read_dir;
use std::fs::DirEntry;
use std::fs::File;
use std::io::Write;
use std::path::Path;

/**
 * This creates a file "test_assert_pass.rs" in the target directory
 * that contains one test case for each .yul file in
 * tests/assert_pass
 */
fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("test_assert_pass.rs");
    let mut test_file = File::create(&destination).unwrap();

    // TODO recursion
    for directory in read_dir("./tests/assert_pass/").unwrap() {
        write_test(&mut test_file, &directory.unwrap());
    }
}

fn write_test(test_file: &mut File, file: &DirEntry) {
    if let Some(file_name) = file
        .file_name()
        .to_str()
        .unwrap()
        .to_string()
        .strip_suffix(".yul")
    {
        let test_name: String = file_name
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();

        write!(
            test_file,
            include_str!("./tests/assert_pass/test.tmpl"),
            name = test_name,
            test_file = file.path().canonicalize().unwrap().display(),
        )
        .unwrap();
    }
}
