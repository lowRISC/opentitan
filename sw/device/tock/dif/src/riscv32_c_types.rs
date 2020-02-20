pub type c_int = i32;
pub type c_uint = u32;
pub type c_longlong = i64;
pub type c_ulonglong = u64;

#[repr(u8)]
pub enum c_void {
    #[doc(hidden)]
    __variant1,
    #[doc(hidden)]
    __variant2,
}
