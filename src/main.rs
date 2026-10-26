fn main() {
    if let Err(error) = vastitas::driver::run(std::env::args_os().skip(1)) {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
