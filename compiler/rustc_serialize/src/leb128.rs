#![macro_use]

use std::io::{BufWriter, Write};
use std::fs::File;

macro_rules! max_leb128_len {
    ($int_ty:ty) => {
        (std::mem::size_of::<$int_ty>() * 8 + 6) / 7
    }
}

pub const fn max_leb128_len() -> usize {
    max_leb128_len!(u128)
}

macro_rules! impl_write_unsigned_leb128_x {
    ($fn_name:ident, $int_ty:ty) => {
        #[inline]
        pub fn $fn_name(
            out: &mut BufWriter<File>,
            mut value: $int_ty,
        ) -> Result<usize, std::io::Error> {
            let mut i = 0;
            loop {
                if value < 0x80 {
                    out.write_all(&[value as u8])?;
                    i += 1;
                    break;
                } else {
                    out.write_all(&[((value & 0x7f) | 0x80) as u8])?;
                    value >>= 7;
                    i += 1;
                }
            }

            Ok(i)
        }
    };
}

impl_write_unsigned_leb128_x!(write_u16_leb128_x, u16);
impl_write_unsigned_leb128_x!(write_u32_leb128_x, u32);
impl_write_unsigned_leb128_x!(write_u64_leb128_x, u64);
impl_write_unsigned_leb128_x!(write_u128_leb128_x, u128);
impl_write_unsigned_leb128_x!(write_usize_leb128_x, usize);


macro_rules! impl_write_unsigned_leb128 {
    ($fn_name:ident, $int_ty:ty) => {
        #[inline]
        pub fn $fn_name(
            out: &mut [::std::mem::MaybeUninit<u8>; max_leb128_len!($int_ty)],
            mut value: $int_ty,
        ) -> usize {
            let mut i = 0;

            loop {
                if value < 0x80 {
                    unsafe {
                        *out.get_unchecked_mut(i).as_mut_ptr() = value as u8;
                    }

                    i += 1;
                    break;
                } else {
                    unsafe {
                        *out.get_unchecked_mut(i).as_mut_ptr() = ((value & 0x7f) | 0x80) as u8;
                    }

                    value >>= 7;
                    i += 1;
                }
            }

            i
        }
    };
}

impl_write_unsigned_leb128!(write_u16_leb128, u16);
impl_write_unsigned_leb128!(write_u32_leb128, u32);
impl_write_unsigned_leb128!(write_u64_leb128, u64);
impl_write_unsigned_leb128!(write_u128_leb128, u128);
impl_write_unsigned_leb128!(write_usize_leb128, usize);

macro_rules! impl_read_unsigned_leb128 {
    ($fn_name:ident, $int_ty:ty) => {
        #[inline]
        pub fn $fn_name(slice: &[u8]) -> ($int_ty, usize) {
            let mut result = 0;
            let mut shift = 0;
            let mut position = 0;
            loop {
                let byte = slice[position];
                position += 1;
                if (byte & 0x80) == 0 {
                    result |= (byte as $int_ty) << shift;
                    return (result, position);
                } else {
                    result |= ((byte & 0x7F) as $int_ty) << shift;
                }
                shift += 7;
            }
        }
    };
}

impl_read_unsigned_leb128!(read_u16_leb128, u16);
impl_read_unsigned_leb128!(read_u32_leb128, u32);
impl_read_unsigned_leb128!(read_u64_leb128, u64);
impl_read_unsigned_leb128!(read_u128_leb128, u128);
impl_read_unsigned_leb128!(read_usize_leb128, usize);

macro_rules! impl_write_signed_leb128 {
    ($fn_name:ident, $int_ty:ty) => {
        #[inline]
        pub fn $fn_name(
            out: &mut [::std::mem::MaybeUninit<u8>; max_leb128_len!($int_ty)],
            mut value: $int_ty,
        ) -> usize {
            let mut i = 0;

            loop {
                let mut byte = (value as u8) & 0x7f;
                value >>= 7;
                let more =
                    !(((value == 0) && ((byte & 0x40) == 0)) || ((value == -1) && ((byte & 0x40) != 0)));

                if more {
                    byte |= 0x80; // Mark this byte to show that more bytes will follow.
                }

                unsafe {
                    *out.get_unchecked_mut(i).as_mut_ptr() = byte;
                }

                i += 1;

                if !more {
                    break;
                }
            }

            i
        }
    }
}

impl_write_signed_leb128!(write_i16_leb128, i16);
impl_write_signed_leb128!(write_i32_leb128, i32);
impl_write_signed_leb128!(write_i64_leb128, i64);
impl_write_signed_leb128!(write_i128_leb128, i128);
impl_write_signed_leb128!(write_isize_leb128, isize);

macro_rules! impl_write_signed_leb128_x {
    ($fn_name:ident, $int_ty:ty) => {
        #[inline]
        pub fn $fn_name(
            out: &mut BufWriter<File>,
            mut value: $int_ty,
        ) -> Result<usize, std::io::Error> {
            let mut i = 0;

            loop {
                let mut byte = (value as u8) & 0x7f;
                value >>= 7;
                let more =
                    !(((value == 0) && ((byte & 0x40) == 0)) || ((value == -1) && ((byte & 0x40) != 0)));

                if more {
                    byte |= 0x80; // Mark this byte to show that more bytes will follow.
                }

                out.write_all(&[byte])?;
                i += 1;

                if !more {
                    break;
                }
            }

            Ok(i)
        }
    }
}

impl_write_signed_leb128_x!(write_i16_leb128_x, i16);
impl_write_signed_leb128_x!(write_i32_leb128_x, i32);
impl_write_signed_leb128_x!(write_i64_leb128_x, i64);
impl_write_signed_leb128_x!(write_i128_leb128_x, i128);
impl_write_signed_leb128_x!(write_isize_leb128_x, isize);

#[inline]
pub fn read_signed_leb128(data: &[u8], start_position: usize) -> (i128, usize) {
    let mut result = 0;
    let mut shift = 0;
    let mut position = start_position;
    let mut byte;

    loop {
        byte = data[position];
        position += 1;
        result |= i128::from(byte & 0x7F) << shift;
        shift += 7;

        if (byte & 0x80) == 0 {
            break;
        }
    }

    if (shift < 64) && ((byte & 0x40) != 0) {
        // sign extend
        result |= -(1 << shift);
    }

    (result, position - start_position)
}
