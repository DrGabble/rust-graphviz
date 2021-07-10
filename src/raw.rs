#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused)]
#![allow(unknown_lints)]
#![allow(deref_nullptr)]

// https://rust-lang.github.io/rust-bindgen/library-usage.html
// https://www.graphviz.org/pdf/libguide.pdf
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

macro_rules! to_c_str {
    ($string:literal) => {
        std::ffi::CStr::from_bytes_with_nul($string.as_bytes()).unwrap()
    };
    ($string:expr) => {
        std::ffi::CString::new($string).unwrap()
    };
}
