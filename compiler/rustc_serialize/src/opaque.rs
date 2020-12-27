use crate::leb128::{self, max_leb128_len, read_signed_leb128};
use crate::serialize;
use std::borrow::Cow;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::mem::MaybeUninit;
use std::ptr;

// -----------------------------------------------------------------------------
// Encoder
// -----------------------------------------------------------------------------

pub trait OpaqueEncoder: serialize::Encoder {
    fn emit_raw_bytes(&mut self, s: &[u8]) -> Result<(), <Self as serialize::Encoder>::Error>;
    fn position(&self) -> usize;
}

pub type EncodeResult = Result<(), !>;

pub struct Encoder {
    pub data: Vec<u8>,
}

impl Encoder {
    pub fn new(data: Vec<u8>) -> Encoder {
        Encoder { data }
    }

    pub fn into_inner(self) -> Vec<u8> {
        self.data
    }

    #[inline]
    pub fn emit_raw_bytes(&mut self, s: &[u8]) {
        self.data.extend_from_slice(s);
    }
}

macro_rules! write_leb128 {
    ($enc:expr, $value:expr, $int_ty:ty, $fun:ident) => {{
        const MAX_ENCODED_LEN: usize = max_leb128_len!($int_ty);
        let old_len = $enc.data.len();

        if MAX_ENCODED_LEN > $enc.data.capacity() - old_len {
            $enc.data.reserve(MAX_ENCODED_LEN);
        }

        // SAFETY: The above check and `reserve` ensures that there is enough
        // room to write the encoded value to the vector's internal buffer.
        unsafe {
            let buf = &mut *($enc.data.as_mut_ptr().add(old_len)
                as *mut [MaybeUninit<u8>; MAX_ENCODED_LEN]);
            let encoded_len = leb128::$fun(buf, $value);
            $enc.data.set_len(old_len + encoded_len);
        }

        Ok(())
    }};
}

impl serialize::Encoder for Encoder {
    type Error = !;

    #[inline]
    fn emit_unit(&mut self) -> EncodeResult {
        Ok(())
    }

    #[inline]
    fn emit_usize(&mut self, v: usize) -> EncodeResult {
        write_leb128!(self, v, usize, write_usize_leb128)
    }

    #[inline]
    fn emit_u128(&mut self, v: u128) -> EncodeResult {
        write_leb128!(self, v, u128, write_u128_leb128)
    }

    #[inline]
    fn emit_u64(&mut self, v: u64) -> EncodeResult {
        write_leb128!(self, v, u64, write_u64_leb128)
    }

    #[inline]
    fn emit_u32(&mut self, v: u32) -> EncodeResult {
        write_leb128!(self, v, u32, write_u32_leb128)
    }

    #[inline]
    fn emit_u16(&mut self, v: u16) -> EncodeResult {
        write_leb128!(self, v, u16, write_u16_leb128)
    }

    #[inline]
    fn emit_u8(&mut self, v: u8) -> EncodeResult {
        self.data.push(v);
        Ok(())
    }

    #[inline]
    fn emit_isize(&mut self, v: isize) -> EncodeResult {
        write_leb128!(self, v, isize, write_isize_leb128)
    }

    #[inline]
    fn emit_i128(&mut self, v: i128) -> EncodeResult {
        write_leb128!(self, v, i128, write_i128_leb128)
    }

    #[inline]
    fn emit_i64(&mut self, v: i64) -> EncodeResult {
        write_leb128!(self, v, i64, write_i64_leb128)
    }

    #[inline]
    fn emit_i32(&mut self, v: i32) -> EncodeResult {
        write_leb128!(self, v, i32, write_i32_leb128)
    }

    #[inline]
    fn emit_i16(&mut self, v: i16) -> EncodeResult {
        write_leb128!(self, v, i16, write_i16_leb128)
    }

    #[inline]
    fn emit_i8(&mut self, v: i8) -> EncodeResult {
        let as_u8: u8 = unsafe { std::mem::transmute(v) };
        self.emit_u8(as_u8)
    }

    #[inline]
    fn emit_bool(&mut self, v: bool) -> EncodeResult {
        self.emit_u8(if v { 1 } else { 0 })
    }

    #[inline]
    fn emit_f64(&mut self, v: f64) -> EncodeResult {
        let as_u64: u64 = v.to_bits();
        self.emit_u64(as_u64)
    }

    #[inline]
    fn emit_f32(&mut self, v: f32) -> EncodeResult {
        let as_u32: u32 = v.to_bits();
        self.emit_u32(as_u32)
    }

    #[inline]
    fn emit_char(&mut self, v: char) -> EncodeResult {
        self.emit_u32(v as u32)
    }

    #[inline]
    fn emit_str(&mut self, v: &str) -> EncodeResult {
        self.emit_usize(v.len())?;
        self.emit_raw_bytes(v.as_bytes());
        Ok(())
    }
}

impl OpaqueEncoder for Encoder {
    #[inline]
    fn emit_raw_bytes(&mut self, s: &[u8]) -> Result<(), <Self as serialize::Encoder>::Error> {
        Encoder::emit_raw_bytes(self, s);
        Ok(())
    }

    #[inline]
    fn position(&self) -> usize {
        self.data.len()
    }
}

pub type FileEncodeResult = Result<(), io::Error>;

pub struct FileEncoder {
    buf: Box<[MaybeUninit<u8>]>,
    used: usize,
    position: usize,
    file: File,
}

impl FileEncoder {
    pub fn new(writer: BufWriter<File>) -> Self {
        // Require capacity at least as large as the largest LEB128 encoding
        // here so that we don't have to check or handle this on every write.
        assert!(writer.capacity() >= max_leb128_len());

        FileEncoder {
            buf: Box::new_uninit_slice(writer.capacity()),
            used: 0,
            position: 0,
            file: writer.into_inner().unwrap(),
        }
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.buf.len()
    }

    #[inline]
    fn write_one(&mut self, value: u8) -> FileEncodeResult {
        // This is only a debug assert because we already ensured this in `new`.
        debug_assert!(self.capacity() >= 1);

        let mut used = self.used;

        if used >= self.capacity() {
            self.flush()?;
            used = 0;
        }

        // SAFETY: The above check and `flush` ensures that there is enough
        // room to write the input buffer to the buffer.
        unsafe {
            *MaybeUninit::slice_as_mut_ptr(&mut self.buf).add(used) = value;
        }

        self.used = used + 1;
        self.position += 1;

        Ok(())
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> FileEncodeResult {
        let capacity = self.capacity();
        let buf_len = buf.len();
        let mut used = self.used;

        if buf_len <= capacity {
            if buf_len > capacity - used {
                self.flush()?;
                used = 0;
            }

            // SAFETY: The above check and `flush` ensures that there is enough
            // room to write the input buffer to the buffer.
            unsafe {
                let src = buf.as_ptr();
                let dst = MaybeUninit::slice_as_mut_ptr(&mut self.buf).add(used);
                ptr::copy_nonoverlapping(src, dst, buf_len);
            }

            self.used = used + buf_len;
            self.position += buf_len;

            Ok(())
        } else {
            self.write_all_unbuffered(buf)
        }
    }

    // FIXME This method is basically a copy of the default `Write::write_all`
    // implementation that updates `self.position`. It should be removed if and
    // when the `Write` trait gets some form of `write_all` that returns the
    // number of bytes written. We need this information to update the position
    // correctly in the face of errors. We could use `Seek::stream_position` to
    // get the information, but it's not ideal (for one thing, it's fallible).
    //
    // In practice, this is only used when the client supplies an input larger
    // than our `BufWriter`'s buffer, and the hope is that never happens.
    fn write_all_unbuffered(&mut self, mut buf: &[u8]) -> FileEncodeResult {
        debug_assert!(buf.len() > self.capacity());

        if self.used > 0 {
            self.flush()?;
        }

        while !buf.is_empty() {
            match self.file.write(buf) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    ));
                }
                Ok(n) => {
                    buf = &buf[n..];
                    self.position += n;
                }
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }

    fn flush(&mut self) -> FileEncodeResult {
        /// Helper struct to ensure the buffer is updated after all the writes
        /// are complete. It tracks the number of written bytes and drains them
        /// all from the front of the buffer when dropped.
        struct BufGuard<'a> {
            buffer: &'a mut [u8],
            len: &'a mut usize,
            written: usize,
        }

        impl<'a> BufGuard<'a> {
            fn new(buffer: &'a mut [u8], len: &'a mut usize) -> Self {
                Self { buffer, len, written: 0 }
            }

            /// The unwritten part of the buffer
            fn remaining(&self) -> &[u8] {
                &self.buffer[self.written..]
            }

            /// Flag some bytes as removed from the front of the buffer
            fn consume(&mut self, amt: usize) {
                self.written += amt;
            }

            /// true if all of the bytes have been written
            fn done(&self) -> bool {
                self.written >= *self.len
            }
        }

        impl Drop for BufGuard<'_> {
            fn drop(&mut self) {
                if self.written > 0 {
                    if self.done() {
                        *self.len = 0;
                    } else {
                        let left = *self.len - self.written;

                        unsafe {
                            let src = self.buffer.as_ptr().add(self.written);
                            let dst = self.buffer.as_mut_ptr();
                            ptr::copy(src, dst, left);
                        }

                        *self.len = left;
                    }
                }
            }
        }

        // TODO Consider unchecked access.
        let mut guard = BufGuard::new(
            unsafe { MaybeUninit::slice_assume_init_mut(&mut self.buf[..self.used]) },
            &mut self.used,
        );

        while !guard.done() {
            match self.file.write(guard.remaining()) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write the buffered data",
                    ));
                }
                Ok(n) => guard.consume(n),
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }
}

impl Drop for FileEncoder {
    fn drop(&mut self) {
        let _result = self.flush();
    }
}

macro_rules! bufwriter_write_leb128 {
    ($enc:expr, $value:expr, $int_ty:ty, $fun:ident) => {{
        const MAX_ENCODED_LEN: usize = max_leb128_len!($int_ty);

        // This is only a debug assert because we already ensured this in `new`.
        debug_assert!($enc.capacity() >= MAX_ENCODED_LEN);

        let mut used = $enc.used;

        if MAX_ENCODED_LEN > $enc.capacity() - used {
            $enc.flush()?;
            used = 0;
        }

        // SAFETY: The above check and flush ensures that there is enough
        // room to write the encoded value to the buffer.
        let buf = unsafe {
            &mut *($enc.buf.as_mut_ptr().add(used)
                as *mut [MaybeUninit<u8>; MAX_ENCODED_LEN])
        };

        let encoded_len = leb128::$fun(buf, $value);
        $enc.used = used + encoded_len;
        $enc.position += encoded_len;

        Ok(())
    }};
}

impl serialize::Encoder for FileEncoder {
    type Error = io::Error;

    #[inline]
    fn emit_unit(&mut self) -> FileEncodeResult {
        Ok(())
    }

    #[inline]
    fn emit_usize(&mut self, v: usize) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, usize, write_usize_leb128)
    }

    #[inline]
    fn emit_u128(&mut self, v: u128) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, u128, write_u128_leb128)
    }

    #[inline]
    fn emit_u64(&mut self, v: u64) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, u64, write_u64_leb128)
    }

    #[inline]
    fn emit_u32(&mut self, v: u32) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, u32, write_u32_leb128)
    }

    #[inline]
    fn emit_u16(&mut self, v: u16) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, u16, write_u16_leb128)
    }

    #[inline]
    fn emit_u8(&mut self, v: u8) -> FileEncodeResult {
        self.write_one(v)
    }

    #[inline]
    fn emit_isize(&mut self, v: isize) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, isize, write_isize_leb128)
    }

    #[inline]
    fn emit_i128(&mut self, v: i128) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, i128, write_i128_leb128)
    }

    #[inline]
    fn emit_i64(&mut self, v: i64) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, i64, write_i64_leb128)
    }

    #[inline]
    fn emit_i32(&mut self, v: i32) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, i32, write_i32_leb128)
    }

    #[inline]
    fn emit_i16(&mut self, v: i16) -> FileEncodeResult {
        bufwriter_write_leb128!(self, v, i16, write_i16_leb128)
    }

    #[inline]
    fn emit_i8(&mut self, v: i8) -> FileEncodeResult {
        let as_u8: u8 = unsafe { std::mem::transmute(v) };
        self.emit_u8(as_u8)
    }

    #[inline]
    fn emit_bool(&mut self, v: bool) -> FileEncodeResult {
        self.emit_u8(if v { 1 } else { 0 })
    }

    #[inline]
    fn emit_f64(&mut self, v: f64) -> FileEncodeResult {
        let as_u64: u64 = v.to_bits();
        self.emit_u64(as_u64)
    }

    #[inline]
    fn emit_f32(&mut self, v: f32) -> FileEncodeResult {
        let as_u32: u32 = v.to_bits();
        self.emit_u32(as_u32)
    }

    #[inline]
    fn emit_char(&mut self, v: char) -> FileEncodeResult {
        self.emit_u32(v as u32)
    }

    #[inline]
    fn emit_str(&mut self, v: &str) -> FileEncodeResult {
        self.emit_usize(v.len())?;
        self.emit_raw_bytes(v.as_bytes())
    }
}

impl OpaqueEncoder for FileEncoder {
    #[inline]
    fn emit_raw_bytes(&mut self, s: &[u8]) -> FileEncodeResult {
        self.write_all(s)
    }

    #[inline]
    fn position(&self) -> usize {
        self.position
    }
}

// -----------------------------------------------------------------------------
// Decoder
// -----------------------------------------------------------------------------

pub struct Decoder<'a> {
    pub data: &'a [u8],
    position: usize,
}

impl<'a> Decoder<'a> {
    #[inline]
    pub fn new(data: &'a [u8], position: usize) -> Decoder<'a> {
        Decoder { data, position }
    }

    #[inline]
    pub fn position(&self) -> usize {
        self.position
    }

    #[inline]
    pub fn set_position(&mut self, pos: usize) {
        self.position = pos
    }

    #[inline]
    pub fn advance(&mut self, bytes: usize) {
        self.position += bytes;
    }

    #[inline]
    pub fn read_raw_bytes(&mut self, s: &mut [u8]) -> Result<(), String> {
        let start = self.position;
        let end = start + s.len();

        s.copy_from_slice(&self.data[start..end]);

        self.position = end;

        Ok(())
    }
}

macro_rules! read_uleb128 {
    ($dec:expr, $fun:ident) => {{
        let (value, bytes_read) = leb128::$fun(&$dec.data[$dec.position..]);
        $dec.position += bytes_read;
        Ok(value)
    }};
}

macro_rules! read_sleb128 {
    ($dec:expr, $t:ty) => {{
        let (value, bytes_read) = read_signed_leb128($dec.data, $dec.position);
        $dec.position += bytes_read;
        Ok(value as $t)
    }};
}

impl<'a> serialize::Decoder for Decoder<'a> {
    type Error = String;

    #[inline]
    fn read_nil(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    #[inline]
    fn read_u128(&mut self) -> Result<u128, Self::Error> {
        read_uleb128!(self, read_u128_leb128)
    }

    #[inline]
    fn read_u64(&mut self) -> Result<u64, Self::Error> {
        read_uleb128!(self, read_u64_leb128)
    }

    #[inline]
    fn read_u32(&mut self) -> Result<u32, Self::Error> {
        read_uleb128!(self, read_u32_leb128)
    }

    #[inline]
    fn read_u16(&mut self) -> Result<u16, Self::Error> {
        read_uleb128!(self, read_u16_leb128)
    }

    #[inline]
    fn read_u8(&mut self) -> Result<u8, Self::Error> {
        let value = self.data[self.position];
        self.position += 1;
        Ok(value)
    }

    #[inline]
    fn read_usize(&mut self) -> Result<usize, Self::Error> {
        read_uleb128!(self, read_usize_leb128)
    }

    #[inline]
    fn read_i128(&mut self) -> Result<i128, Self::Error> {
        read_sleb128!(self, i128)
    }

    #[inline]
    fn read_i64(&mut self) -> Result<i64, Self::Error> {
        read_sleb128!(self, i64)
    }

    #[inline]
    fn read_i32(&mut self) -> Result<i32, Self::Error> {
        read_sleb128!(self, i32)
    }

    #[inline]
    fn read_i16(&mut self) -> Result<i16, Self::Error> {
        read_sleb128!(self, i16)
    }

    #[inline]
    fn read_i8(&mut self) -> Result<i8, Self::Error> {
        let as_u8 = self.data[self.position];
        self.position += 1;
        unsafe { Ok(::std::mem::transmute(as_u8)) }
    }

    #[inline]
    fn read_isize(&mut self) -> Result<isize, Self::Error> {
        read_sleb128!(self, isize)
    }

    #[inline]
    fn read_bool(&mut self) -> Result<bool, Self::Error> {
        let value = self.read_u8()?;
        Ok(value != 0)
    }

    #[inline]
    fn read_f64(&mut self) -> Result<f64, Self::Error> {
        let bits = self.read_u64()?;
        Ok(f64::from_bits(bits))
    }

    #[inline]
    fn read_f32(&mut self) -> Result<f32, Self::Error> {
        let bits = self.read_u32()?;
        Ok(f32::from_bits(bits))
    }

    #[inline]
    fn read_char(&mut self) -> Result<char, Self::Error> {
        let bits = self.read_u32()?;
        Ok(std::char::from_u32(bits).unwrap())
    }

    #[inline]
    fn read_str(&mut self) -> Result<Cow<'_, str>, Self::Error> {
        let len = self.read_usize()?;
        let s = std::str::from_utf8(&self.data[self.position..self.position + len]).unwrap();
        self.position += len;
        Ok(Cow::Borrowed(s))
    }

    #[inline]
    fn error(&mut self, err: &str) -> Self::Error {
        err.to_string()
    }
}
