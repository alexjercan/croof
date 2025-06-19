use std::{fs::File, io::{self, Read}};

/// Reads the input from a file or standard input.
pub(crate) fn read_input(path: Option<String>) -> io::Result<String> {
    let mut buffer = String::new();

    match path {
        Some(p) => {
            let mut file = File::open(p)?;
            file.read_to_string(&mut buffer)?;
        }
        None => {
            let stdin = io::stdin();
            let mut handle = stdin.lock();
            handle.read_to_string(&mut buffer)?;
        }
    }

    Ok(buffer)
}
