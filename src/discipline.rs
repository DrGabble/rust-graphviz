use std::convert::TryInto;
use std::ffi::{c_void, CStr};

use super::raw;

pub fn string_io() -> raw::Agdisc_t {
    // UNSAFE mutable reference to static, but library doesn't actually mutate
    raw::Agdisc_t {
        mem: std::ptr::null_mut(),
        id: std::ptr::null_mut(),
        io: unsafe { &mut STRING_IO },
    }
}

static mut STRING_IO: raw::Agiodisc_t = raw::Agiodisc_t {
    afread: Some(string_read),
    putstr: Some(string_write),
    flush: Some(string_flush),
};

unsafe extern "C" fn string_read(string_ptr: *mut c_void, data_ptr: *mut i8, data_len: i32) -> i32 {
    0
}

unsafe extern "C" fn string_write(string_ptr: *mut c_void, data_ptr: *const i8) -> i32 {
    if string_ptr.is_null() || data_ptr.is_null() {
        return -1;
    }
    let string = &mut *(string_ptr as *mut String);
    if let Ok(data_string) = CStr::from_ptr(data_ptr).to_str() {
        string.push_str(data_string);
        let bytes_written = data_string.len();
        bytes_written.try_into().unwrap_or(-1)
    } else {
        -1
    }
}

unsafe extern "C" fn string_flush(_: *mut c_void) -> i32 {
    0
}
