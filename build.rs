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
    for dir_name in ["assert_pass", "revert_unreachable", "some_revert_reachable"] {
        let destination = Path::new(&out_dir).join(format!("test_{dir_name}.rs"));
        let mut test_file = File::create(&destination).unwrap();

        // TODO recursion
        for file in read_dir(format!("./tests/{dir_name}/")).unwrap() {
            write_test(&mut test_file, &file.unwrap(), dir_name);
        }
    }
}

fn write_test(test_file: &mut File, file: &DirEntry, test_directory: &str) {
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
            r#"#[test]
fn {test_name}() {{
    test_{test_directory}(include_str!("{test_file}"), "{test_file}");
}}"#,
            test_file = file.path().canonicalize().unwrap().display(),
        )
        .unwrap();
    }
}
