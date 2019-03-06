//! Helpers to write the file.

use byteorder::{BigEndian, LittleEndian, WriteBytesExt};
use std::fs;
use std::io;
use std::io::Write;

/// The byte order used within the TIFF file.
///
/// There are two possible values: II (little-endian or Intel format)
/// and MM (big-endian or Motorola format).
#[derive(Clone, Copy)]
pub enum Endianness {
    /// Intel byte order, also known as little-endian.
    ///
    /// The byte order is always from the least significant byte to
    /// the most significant byte.
    II,

    /// Motorola byte order, also known as big-endian.
    ///
    /// The byte order is always from the most significant byte to
    /// the least significant byte.
    MM,
}

impl Endianness {
    /// Returns the u16 value that represents the given endianness
    /// in a Tagged Image File Header.
    pub(crate) fn id(&self) -> u16 {
        match &self {
            Endianness::II => 0x4949,
            Endianness::MM => 0x4d4d,
        }
    }
}

/// Used during the allocation phase of the process of creating
/// a TIFF file.
///
/// Holds the number of bytes that were allocated, in order to
/// calculate the needed offsets.
#[doc(hidden)]
pub struct Cursor(u32);
impl Cursor {
    /// Creates a new `Cursor` with no bytes allocated.
    pub(crate) fn new() -> Self {
        Cursor(0)
    }

    /// Allocates a number of bytes to the `Cursor`.
    ///
    /// # Panics
    ///
    /// The maximum size of a TIFF file is 2**32 bits. Attempting
    /// to allocate more space than that will `panic`.
    pub(crate) fn allocate(&mut self, n: u32) {
        self.0 = match self.0.checked_add(n) {
            Some(val) => val,
            None => panic!("Attempted to write a TIFF file bigger than 2**32 bytes."),
        };
    }

    /// Returns the number of already allocated bytes.
    pub(crate) fn allocated_bytes(&self) -> u32 {
        self.0
    }
}

/// Helper structure that provides convenience methods to write to
/// a `fs::File`, being aware of the file's [`Endianness`].
///
/// [`Endianness`]: enum.Endianness.html
pub struct EndianFile {
    file: fs::File,
    byte_order: Endianness,
    written_bytes: u32,
}

impl Into<fs::File> for EndianFile {
    fn into(self) -> fs::File {
        self.file
    }
}

impl EndianFile {
    /// Gets the number of written bytes to this file.
    pub(crate) fn new(file: fs::File, byte_order: Endianness) -> Self {
        Self {
            file,
            byte_order,
            written_bytes: 0,
        }
    }

    /// Gets the number of written bytes to this file.
    pub(crate) fn written_bytes(&self) -> u32 {
        self.written_bytes
    }
}

impl EndianFile {
    /// Writes a u8 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u8(&mut self, n: u8) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_u8(n)
    }

    /// Writes a slice of bytes to a file.
    ///
    /// This is much more efficient than calling [`write_u8`] in a loop if you have list
    /// of bytes to write.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_all_u8(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.written_bytes += bytes.len() as u32;
        self.file.write_all(bytes)
    }

    /// Writes a u16 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u16(&mut self, n: u16) -> io::Result<()> {
        self.written_bytes += 2;
        match self.byte_order {
            Endianness::II => {
                self.file.write_u16::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_u16::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a u32 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u32(&mut self, n: u32) -> io::Result<()> {
        self.written_bytes += 4;
        match self.byte_order {
            Endianness::II => {
                self.file.write_u32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_u32::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a i8 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i8(&mut self, n: i8) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_i8(n)
    }

    /// Writes a i16 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i16(&mut self, n: i16) -> io::Result<()> {
        self.written_bytes += 2;
        match self.byte_order {
            Endianness::II => {
                self.file.write_i16::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_i16::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a i32 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i32(&mut self, n: i32) -> io::Result<()> {
        self.written_bytes += 4;
        match self.byte_order {
            Endianness::II => {
                self.file.write_i32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_i32::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a f32 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_f32(&mut self, n: f32) -> io::Result<()> {
        self.written_bytes += 4;
        match self.byte_order {
            Endianness::II => {
                self.file.write_f32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_f32::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a f64 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_f64(&mut self, n: f64) -> io::Result<()> {
        self.written_bytes += 8;
        match self.byte_order {
            Endianness::II => {
                self.file.write_f64::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_f64::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes an arbitraty byte to the file.
    ///
    /// This is useful when there is need to write an extra byte
    /// to guarantee that all offsets are even but that byte
    /// doesn't really hold any information.
    pub(crate) fn write_arbitrary_byte(&mut self) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_u8(0)
    }
}
