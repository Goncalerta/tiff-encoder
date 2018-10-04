//! A crate for encoding TIFF files.
//! 
//! This crate allows to create any hierarchy of IFDs and to add any
//! tags with any values to each. It does so while avoiding that
//! the user needs to worry about the position of each structure in the
//! file and to point to it with the correct offset.
//! 
//! The main structure of this crate, used to actually write the TIFF
//! file, the is [`TiffFile`]. This structure writes the file in [little endian]
//! by default (but that can be changed) and requires an [`IfdChain`]. This
//! `IfdChain` consists of the first [`Ifd`] of the file, the one it points to (if any), 
//! and so on. Each `Ifd` has one or more entries, which are represented 
//! by a pair of [`FieldTag`] and [`FieldValues`].
//! 
//! # Examples
//! 
//! Creating a 256x256 bilevel image with every pixel black.
//! 
//! ```
//! use tiff_encoder::*;
//! use tiff_encoder::tiff_type::*;
//! 
//! // 256*256/8 = 8192
//! // The image data will have 8192 bytes with 0 in every bit (each representing a
//! // black pixel).
//! let image_data = vec![0x00; 8192];
//! 
//! TiffFile::new(
//!     Ifd::new()
//!         .with_entry(tag::PhotometricInterpretation, SHORT::single(1)) // Black is zero
//!         .with_entry(tag::Compression, SHORT::single(1)) // No compression
//!
//!         .with_entry(tag::ImageLength, LONG::single(256))
//!         .with_entry(tag::ImageWidth, LONG::single(256))
//!
//!         .with_entry(tag::ResolutionUnit, SHORT::single(1)) // No resolution unit
//!         .with_entry(tag::XResolution, RATIONAL::single(1, 1))
//!         .with_entry(tag::YResolution, RATIONAL::single(1, 1))
//!
//!         .with_entry(tag::RowsPerStrip, LONG::single(256)) // One strip for the whole image
//!         .with_entry(tag::StripByteCounts, LONG::single(8192)) 
//!         .with_entry(tag::StripOffsets, ByteBlock::single(image_data))
//!         .single() // This is the only Ifd in its IfdChain
//! ).write_to("example.tif").unwrap();
//! ```
//! 
//! [`TiffFile`]: struct.TiffFile.html
//! [little endian]: enum.Endianness.html#variant.II
//! [`Ifd`]: struct.Ifd.html
//! [`IfdChain`]: struct.IfdChain.html
//! [`FieldTag`]: type.FieldTag.html
//! [`FieldValues`]: trait.FieldValues.html

extern crate byteorder;

pub mod tiff_type;
pub mod tag;

use std::fs;
use std::io;
use byteorder::{WriteBytesExt, LittleEndian, BigEndian};
use std::collections::BTreeMap;
use tiff_type::*;

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
    fn id(&self) -> u16 {
        match &self {
            Endianness::II => 0x4949,
            Endianness::MM => 0x4d4d,
        }
    }
}

/// A helper structure that provides convenience methods to write to
/// a `fs::File`, being aware of the file's [`Endianness`].
/// 
/// [`Endianness`]: enum.Endianness.html
pub struct EndianFile {
    file: fs::File,
    byte_order: Endianness,
    written_bytes: u32,
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
            },
            Endianness::MM => {
                self.file.write_u16::<BigEndian>(n)?;
            },
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
            },
            Endianness::MM => {
                self.file.write_u32::<BigEndian>(n)?;
            },
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
            },
            Endianness::MM => {
                self.file.write_i16::<BigEndian>(n)?;
            },
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
            },
            Endianness::MM => {
                self.file.write_i32::<BigEndian>(n)?;
            },
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
            },
            Endianness::MM => {
                self.file.write_f32::<BigEndian>(n)?;
            },
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
            },
            Endianness::MM => {
                self.file.write_f64::<BigEndian>(n)?;
            },
        }
        Ok(())
    }

    /// Writes an arbitraty byte to the file.
    /// 
    /// This is useful when there is need to write an extra byte
    /// to guarantee that all offsets are even but that byte
    /// doesn't really hold any information.
    fn write_arbitrary_byte(&mut self) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_u8(0)
    }

    /// Gets the number of written bytes to this file.
    fn written_bytes(&mut self) -> u32 {
        self.written_bytes
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
    fn new() -> Self {
        Cursor(0)
    }

    /// Allocates a number of bytes to the `Cursor`.
    /// 
    /// # Panics
    /// 
    /// The maximum size of a TIFF file is 2**32 bits. Attempting
    /// to allocate more space than that will `panic`.
    fn allocate(&mut self, n: u32) {
        self.0 = match self.0.checked_add(n) {
            Some(val) => val,
            None => panic!("Attempted to write a TIFF file bigger than 2**32 bytes."),
        };
    }

    /// Returns the number of already allocated bytes.
    fn allocated_bytes(&self) -> u32 {
        self.0
    }
}

/// Representation of a Tagged Image File.
/// 
/// This is the central structure of the crate. It holds all the other structures
/// of the TIFF file and is responsible for writing them to a `fs::File`.
pub struct TiffFile {
    header: TiffHeader,
    ifds: IfdChain,
}

impl TiffFile {

    /// Creates a new `TiffFile` from an [`IfdChain`].
    /// 
    /// By default, a `TiffFile` is little-endian and has 42 as the magic number.
    /// If you want to change the endianness, consider chaining this function wih
    /// [`with_endianness`].
    /// 
    /// # Examples
    /// 
    /// Creating the simplest valid `TiffFile`: a single [`Ifd`] with only one entry.
    /// ```
    /// use tiff_encoder::*;
    /// use tiff_encoder::tiff_type::*;
    /// let tiff_file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// );
    /// ```
    /// [`Ifd`]: struct.Ifd.html
    /// [`IfdChain`]: struct.IfdChain.html
    /// [`with_endianness`]: #method.with_endianness
    pub fn new(ifds: IfdChain) -> TiffFile {
        TiffFile {
            header: TiffHeader {
                byte_order: Endianness::II,
                magic_number: 42,
            },

            ifds: ifds,
        }
    }

    /// Returns the same `TiffFile`, but with the specified `Endianness`.
    /// 
    /// # Examples
    /// 
    /// As this method returns `Self`, it can be chained when
    /// building a `TiffFile`.
    /// ```
    /// use tiff_encoder::*;
    /// use tiff_encoder::tiff_type::*;
    /// 
    /// let tiff_file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// ).with_endianness(Endianness::MM);
    /// ```
    pub fn with_endianness(mut self, endian: Endianness) -> Self {
        self.header.byte_order = endian;
        self
    }

    /// Writes the `TiffFile` content to a new file created at the given path.
    /// 
    /// Doing so consumes the `TiffFile`. Returns the new `fs::File` wrapped in
    /// an `io::Result`.
    /// 
    /// # Examples
    /// 
    /// Note that, in this example, `file` is a `fs::File`, not a `TiffFile`.
    /// ```
    /// use tiff_encoder::*;
    /// use tiff_encoder::tiff_type::*;
    /// 
    /// let file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// ).write_to("file.tif").unwrap();
    /// ```
    /// 
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    /// 
    /// # Panics
    /// 
    /// This function will `panic` if the file trying to be written would exceed
    /// the maximum size of a TIFF file (2**32 bytes, or 4 GiB). 
    pub fn write_to(self, file_path: &str) -> io::Result<fs::File> {
        let file = fs::File::create(file_path)?;
        // Writing to a file is comprised of two phases: the "Allocating Phase" 
        // and the "Writting Phase". During the first, all the components of the
        // TiffFile allocate their space and become aware of the offsets to other
        // components that they might need to know. In the "Writting Phase", the 
        // components actually write their information to the file they've been 
        // allocated to.
        self.allocate(file).write()
    }

    /// Allocates all of its components to the given file, transforming
    /// itself into an `AllocatedTiffFile`.
    fn allocate(self, file: fs::File) -> AllocatedTiffFile {
        let mut c = Cursor::new();
        let header = self.header.allocate(&mut c);
        let ifds = self.ifds.allocate(&mut c);
        let file = EndianFile {
            file,
            byte_order: header.byte_order,
            written_bytes: 0,
        };
        
        AllocatedTiffFile {
            header,
            ifds,
            file,
        }
    }
}

/// Representation of a TiffFile that called `allocate(&str)` and is
/// ready to `write()`.
struct AllocatedTiffFile {
    header: AllocatedTiffHeader,
    ifds: AllocatedIfdChain,
    file: EndianFile,
}

impl AllocatedTiffFile {
    /// Writes all of its components to the file it has been allocated to.
    fn write(mut self) -> io::Result<fs::File> {
        
        self.header.write_to(&mut self.file)?;
        self.ifds.write_to(&mut self.file)?;
        
        Ok(self.file.file)
    }
}


/// Representation of the Header of a TIFF file.
struct TiffHeader {
    byte_order: Endianness,
    magic_number: u16,
}

impl TiffHeader {
    /// Allocates its space, moving the given `Cursor` forwards, and becomes
    /// aware of the offset to ifd0. 
    /// 
    /// Calling this will transform `self` into an `AllocatedTiffHeader`.
    fn allocate(self, c: &mut Cursor) -> AllocatedTiffHeader {
        c.allocate(8);
        AllocatedTiffHeader {
            byte_order: self.byte_order,
            magic_number: self.magic_number,
            offset_to_ifd0: c.allocated_bytes(),
        }
    }
}

/// Representation of a TiffHeader that called `allocate(&mut Cursor)` and is
/// ready to write to a file.
struct AllocatedTiffHeader {
    byte_order: Endianness,
    magic_number: u16,
    offset_to_ifd0: u32,
}

impl AllocatedTiffHeader {
    /// Write this header to the given `EndianFile`.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        file.write_u16(self.byte_order.id())?;
        file.write_u16(self.magic_number)?;
        file.write_u32(self.offset_to_ifd0)?;
        
        Ok(())
    }
}


/// An ordered list of [`Ifd`]s, each pointing to the next one.
/// 
/// The last `Ifd` doesn't point to any other. 
/// 
/// Because any IFD could technically point to a next one, in most 
/// functions that one would expect to input an `Ifd`, its parameters 
/// actually ask for an `IfdChain`.
/// 
/// [`Ifd`]: struct.Ifd.html
pub struct IfdChain(Vec<Ifd>);
impl IfdChain {
    /// Creates a new `IfdChain` from a vector of [`Ifd`]s.
    ///  
    /// # Panics
    /// 
    /// The TIFF specification requires that each IFD must have at least one entry.
    /// 
    /// Trying to create an `IfdChain` with one or more empty `Ifd`s will `panic`.
    /// 
    /// [`Ifd`]: struct.Ifd.html
    pub fn new(ifds: Vec<Ifd>) -> IfdChain {
        if ifds.len() == 0 { panic!("Cannot create a chain without IFDs.") } 
        for ifd in ifds.iter() {
            if ifd.entry_count() == 0 {
                panic!("Tried to create a chain containing empty IFDs.\nEach IFD must have at least 1 entry.")
            } 
        }
        IfdChain(ifds)
    }

    /// Creates a new `IfdChain` from a single [`Ifd`].
    /// 
    /// # Panics
    /// 
    /// The TIFF specification requires that each IFD must have at least one entry.
    /// 
    /// Trying to create an `IfdChain` from an empty `Ifd` will `panic`.
    /// 
    /// 
    /// [`Ifd`]: struct.Ifd.html
    pub fn single(ifd: Ifd) -> IfdChain {
        IfdChain::new(vec![ifd])
    }

    /// Allocates every `Ifd` in the chain, moving the given `Cursor` forwards.
    /// 
    /// Calling this will transform `self` into an `AllocatedIfdChain`.
    fn allocate(self, c: &mut Cursor) -> AllocatedIfdChain {
        let len = self.0.len();
        let mut ifds = Vec::with_capacity(len);
        for (index, ifd) in self.0.into_iter().enumerate() {
            ifds.push(ifd.allocate(c, index+1 == len));
        }
        AllocatedIfdChain(ifds)
    } 
}

/// An `IfdChain` that called `allocate(&mut Cursor)` and is
/// ready to write to a file.
struct AllocatedIfdChain(Vec<AllocatedIfd>);
impl AllocatedIfdChain {
    /// Write all of the `IFD`s in this chain to the given `EndianFile`.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        for ifd in self.0.into_iter() {
            ifd.write_to(file)?;
        }
        Ok(())
    }
}

/// A structure that holds both an IFD and all the values pointed at
/// by its entries.
/// 
/// In a TIFF file, an IFD may point to another IFD with its last 4
/// bytes. To abstract the user of this crate from the position of each
/// structure in the file, this link between `Ifd`s is represented by
/// an [`IfdChain`]. Because any IFD could technically point to a next
/// one, in most functions that one would expect to input an `Ifd`, its
/// parameters actually ask for an `IfdChain`.
/// 
/// One can easily create an `IfdChain` of a single `Ifd` calling the
/// method [`single()`] on that Ifd.
/// 
/// [`IfdChain`]: struct.IfdChain.html
/// [`single()`]: #method.single
pub struct Ifd {
    entries: BTreeMap<FieldTag, Box<FieldValues>>,
}
impl Ifd {
    /// Creates a new empty `Ifd`.
    ///  
    /// Note that an empty IFD is prohibited by the TIFF specification.
    /// As such, it is not possible to directly use the resulting `Ifd` 
    /// alone in the creation of a TIFF file.
    /// 
    /// However, one can chain this function with methods such as 
    /// [`with_entry(FieldTag, FieldValues)`] in order to build a valid `Ifd`.
    /// 
    /// [`with_entry(FieldTag, FieldValues)`]: #method.with_entry
    pub fn new() -> Ifd {
        Ifd {
            entries: BTreeMap::new(),
        }
    }

    /// Returns the same `Ifd`, but adding the given pair of Tag and Values.
    /// 
    /// Because it returns `Self`, it is possible to chain this method.
    /// 
    /// # Examples
    /// 
    /// Creating a [`TiffFile`] with some arbitrary entries.
    /// 
    /// Note that the order in which entries are added is irrelevant. Internally, 
    /// the `Ifd` will automatically arrange them by ascending order of tags, as
    /// specified by the TIFF specification.
    /// 
    /// ```
    /// use tiff_encoder::*;
    /// use tiff_encoder::tiff_type::*;
    /// 
    /// let ifd = Ifd::new()
    ///     .with_entry(0x0000, BYTE::single(0))
    ///     .with_entry(0x00FF, LONG::single(500))
    ///     .with_entry(0xA01F, SHORT::values(vec![50, 2, 0, 3]))
    ///     .with_entry(0x0005, ASCII::from_str("Hello TIFF!"))
    ///     .with_entry(0x0100, UNDEFINED::values(vec![0x42, 0x42, 0x42, 0x42]));
    /// ```
    /// 
    /// # Panics 
    /// 
    /// In order to protect the user of this crate, trying to add a value
    /// to an already existing entry with this method is considered a mistake 
    /// and will `panic`.
    /// 
    /// Other functions that insert members to the `Ifd` will have an "Entries" 
    /// section, where they'll specify which entries are inserted.
    /// 
    /// [`TiffFile`]: struct.TiffFile.html
    pub fn with_entry<T: FieldValues + 'static>(mut self, tag: FieldTag, value: T) -> Self {
        if self.entries.insert(tag, Box::new(value)).is_some() {
            panic!("Tried to add the same tag twice.");
        }
        self
    }

    /// Returns the same `Ifd`, but adding the given subifds.
    /// 
    /// Because it returns `Self`, it is possible to chain this method.
    /// 
    /// # Entries
    /// 
    /// Using this method will automatically insert the entry 0x014A (tag::SubIFDs).
    /// 
    /// # Panics 
    /// 
    /// If the inserted entries already exist, this function will `panic`.
    /// 
    /// [`TiffFile`]: struct.TiffFile.html
    pub fn with_subifds(self, subifds: Vec<IfdChain>) -> Self {
        self.with_entry(tag::SubIFDs, OffsetsToIfds::new(subifds))
    }

    /// Returns an [`IfdChain`] containing solely this `Ifd`.
    /// 
    /// In other words, it marks this `Ifd` as the single element
    /// of its chain.
    /// 
    /// [`IfdChain`]: struct.IfdChain.html
    pub fn single(self) -> IfdChain {
        IfdChain::single(self)
    }

    /// Returns the number of entries present in this `Ifd`.
    fn entry_count(&self) -> u32 {
        self.entries.len() as u32
    }

    /// Returns the number of bytes occupied by this `Ifd` in its binary form.
    /// 
    /// Note that this only includes the IFD itself, not the values associated
    /// with it that don't fit in their entry nor the blocks of data pointed at by
    /// some of the fields.
    fn size(&self) -> u32 {
        self.entry_count() * 12 + 6
    }

    /// Allocates space in the given `Cursor` for this `Ifd`, as well as 
    /// the field values associated with it that don't fit in their entry.
    /// 
    /// Becomes aware of the position of the next IFD in its chain (if 
    /// its not the last IFD), thus transforming into an `AllocatedIFd`.
    fn allocate(self, c: &mut Cursor, last_ifd: bool) -> AllocatedIfd {
        c.allocate(self.size());
        
        let mut entries = BTreeMap::new();
        for (tag, value) in self.entries {
            entries.insert(tag, value.allocate(c));
        }
        
        let offset_to_next_ifd = if last_ifd {
           None
        } else {
           Some(c.allocated_bytes())
        };

        AllocatedIfd {
            entries,
            offset_to_next_ifd,
        }
    }
}

/// Representation of a `Ifd` that called `allocate(&mut Cursor, bool)` and is
/// ready to write to a file.
struct AllocatedIfd {
    entries: BTreeMap<FieldTag, Box<AllocatedFieldValues>>,
    offset_to_next_ifd: Option<u32>,
}

impl AllocatedIfd {
    /// Write this IFD to the given `EndianFile`, as well as any values
    /// associated with its entries.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        let mut big_values = Vec::new();

        file.write_u16(self.entries.len() as u16)?;
        
        for (tag, value) in self.entries.into_iter() {
            let value = Self::write_entry_to((tag, value), file)?;
            if let Some(value) = value {
                big_values.push(value);
            }
        }
        file.write_u32(self.offset_to_next_ifd.unwrap_or(0))?;
        
        for value in big_values {
            value.write_to(file)?;
        }

        Ok(())
    }

    /// Write a single entry of the IFD. If its value doesn't fit,
    /// returns that value back so it can be written later, after
    /// the IFD.
    fn write_entry_to((tag, value): (FieldTag, Box<AllocatedFieldValues>), file: &mut EndianFile) 
    -> io::Result<Option<Box<AllocatedFieldValues>>> {
        file.write_u16(tag)?;
        file.write_u16(value.type_id())?;
        file.write_u32(value.count())?;
        
        match value.position() {
            Some(position) => {
                file.write_u32(position)?;
                Ok(Some(value))
            },
            None => {
                let size = value.size();
                value.write_to(file)?;
                for _ in 0..(4-size) {
                    file.write_u8(0)?;
                }
                Ok(None)
            }
        }
    }
}

/// 16-bit identifier of a field entry.
/// 
/// The module [`tag`] has some constants for commonly used
/// `FieldTag`s.
/// 
/// [`tag`]: ./tag/index.html
pub type FieldTag = u16;

/// Seals FieldValues, so that it can only be implemented inside
/// the crate. There are only three types of FieldValues:
/// `Offsets` to datablocks, `OffsetsToIfds` and `TiffTypeValues`.
mod private {
    pub trait Sealed {}
    impl<T: super::Datablock> Sealed for super::Offsets<T> {}
    impl<T: super::TiffType> Sealed for super::TiffTypeValues<T> {}
    impl Sealed for super::OffsetsToIfds {}
}

/// The values contained or pointed at by an IFD Field.
/// 
/// There are three groups of `FieldValues`: [`TiffTypeValues`],
/// [`Offsets`] and [`OffsetsToIfds`]. The first represents a list 
/// of values of any given [`TiffType`]. The second represents a 
/// list of [`LONG`] values, each pointing to a specific [`Datablock`].
/// The third represents a list of [`IFD`] values, each pointing to
/// an [`Ifd`].
/// 
/// It is not possible to implement this trait manually outside of
/// this crate.
/// 
/// [`TiffTypeValues`]: struct.TiffTypeValues.html
/// [`Offsets`]: struct.Offsets.html
/// [`OffsetsToIfds`]: struct.OffsetsToIfds.html
/// [`TiffType`]: tiff_type/trait.TiffType.html
/// [`LONG`]:tiff_type/struct.LONG.html
/// [`IFD`]:tiff_type/struct.IFD.html
/// [`Datablock`]: trait.Datablock.html
pub trait FieldValues: private::Sealed {
    /// The number of values the field contains.
    #[doc(hidden)]
    fn count(&self) -> u32;
    /// The sum of the size of every value in this field.
    /// 
    /// This doesn't include `Datablocks` owned by this field.
    #[doc(hidden)]
    fn size(&self) -> u32;
    /// Allocates the needed space in the given `Cursor`, transforming into
    /// an `AllocatedFieldValues`.
    #[doc(hidden)]
    fn allocate(self: Box<Self>, c: &mut Cursor) -> Box<AllocatedFieldValues>;
}

/// Allocated form of `FieldValues`
#[doc(hidden)]
pub trait AllocatedFieldValues {
    /// The number of values the field contains.
    fn count(&self) -> u32;
    /// The sum of the size of every value in this field.
    /// 
    /// This doesn't include `Datablocks` owned by this field.
    fn size(&self) -> u32;
    /// The offset to the first value (counting from the beginning of the file) 
    /// if the values don't fit in the IFD entry (in other words, if `size()` is
    /// bigger than 4 bytes).
    fn position(&self) -> Option<u32>;
    /// The TIFF 16-bit code that identifies the type of the values of the field.
    fn type_id(&self) -> u16;
    /// Write the values to the given `EndianFile`, as well as any other data
    /// they point to.
    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()>;
}

/// A block of data in the file pointed to by a field value, but
/// that isn't part of the field itself (such as image strips).
/// 
/// It is also possible to store any block of data in a [`ByteBlock`],
/// but that would require to know the [`Endianness`] of the file
/// beforehand, so the bytes are written in the correct order.
/// 
/// Using a `Datablock`, on the other hand, allows to make use
/// of the functionality of an [`EndianFile`], so the data can be
/// written without worrying about the endianness.
/// 
/// [`ByteBlock`]: struct.ByteBlock.html
/// [`Endianness`]: enum.Endianness.html
pub trait Datablock {
    /// The number of bytes occupied by this `Datablock`.
    /// 
    /// # Panics
    /// 
    /// The number of written bytes to the [`EndianFile`] in 
    /// [`write_to(self, &mut EndianFile)`] must be the same value returned 
    /// by this function.
    /// 
    /// Failing to meet that specification will `panic`.
    /// 
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`write_to(self, &mut EndianFile)`]: #method.write_to
    fn size(&self) -> u32;

    /// Writes this `Datablock` to an [`EndianFile`]. The number of bytes 
    /// written must be exactly same number as returned by [`size(&self)`].
    /// 
    /// # Panics
    /// 
    /// Failing to write the exact same number of bytes as indicated in
    /// [`size(&self)`] will `panic`.
    /// 
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`size(&self)`]: #method.size
    fn write_to(self, file: &mut EndianFile) -> io::Result<()>;
}

/// A list of [`IFD`] values, each pointing to a specific 
/// [`Ifd`].
/// 
/// This structure owns a list of [`IfdChain`]s instead, so the user
/// doesn't have to deal with the offsets in the file. Each [`IFD`] 
/// value will point to the first element of each [`IfdChain`]. Each
/// of those `Ifd`s will point to the next one in their chain (if they
/// are not the last of their chain) and so on.
/// 
/// It is responsible for writing both the offsets and all the [`Ifd`]s.
/// 
/// [`LONG`]:tiff_type/struct.LONG.html
/// [`IFD`]:tiff_type/struct.IFD.html
/// [`Ifd`]: struct.Ifd.html
/// [`IfdChain`]: struct.IfdChain.html
pub struct OffsetsToIfds {
    pub data: Vec<IfdChain>,
}
impl OffsetsToIfds {
    /// Creates a new `OffsetsToIfds` instance from a vector of [`IfdChain`]s.
    /// 
    /// [`IfdChain`]: struct.IfdChain.html
    pub fn new(ifds: Vec<IfdChain>) -> Self {
        OffsetsToIfds {
            data: ifds,
        }
    }
}
impl FieldValues for OffsetsToIfds {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        IFD::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor) -> Box<AllocatedFieldValues> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            // If there is just one block, the position will point directly at it.
            // As such, the offsets vector will be kept empty.
            let offsets = Vec::new();
            let ifd = self.data.into_iter().next().unwrap(); // Data has size of 1
            let allocated_data = vec![ifd.allocate(c)];
            
            Box::new(AllocatedOffsetsToIfds {
                position,
                offsets,
                data: allocated_data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());
            let mut allocated_data = Vec::with_capacity(self.data.len());

            for ifd in self.data {
                offsets.push(IFD(c.allocated_bytes()));
                allocated_data.push(ifd.allocate(c));
            }

            Box::new(AllocatedOffsetsToIfds {
                position,
                offsets,
                data: allocated_data,
            })
        }
    }
}

/// Allocated form of `OffsetsToIfds`
struct AllocatedOffsetsToIfds {
    position: Option<u32>,
    offsets: Vec<IFD>,
    data: Vec<AllocatedIfdChain>,
}
impl AllocatedFieldValues for AllocatedOffsetsToIfds {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        IFD::size() * self.count()
    }

    fn position(&self) -> Option<u32> {
        self.position
    }

    fn type_id(&self) -> u16 {
        IFD::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let Self { data, offsets, ..} = unboxed;
        for offset in offsets {
            offset.write_to(file)?;
        }
        for ifd in data.into_iter() {
            ifd.write_to(file)?;
        }
        
        Ok(())
    }
}

/// A list of [`LONG`] values, each pointing to a specific 
/// [`Datablock`].
/// 
/// This structure owns the list of Datablocks instead, so the user
/// doesn't have to deal with the offsets in the file. It is responsible
/// for writing both the offsets and the blocks of data.
/// 
/// [`LONG`]:tiff_type/struct.LONG.html
/// [`Datablock`]: trait.Datablock.html
pub struct Offsets<T: Datablock> {
    pub data: Vec<T>,
}
impl<T: Datablock + 'static> Offsets<T> {
    /// Creates a new `Offsets` instance from a vector of [`Datablock`]s.
    /// 
    /// [`Datablock`]: trait.Datablock.html
    pub fn new(datablocks: Vec<T>) -> Self {
        Offsets {
            data: datablocks,
        }
    }

    /// Creates a new `Offsets` instance from a single [`Datablock`].
    /// 
    /// [`Datablock`]: trait.Datablock.html
    pub fn single(datablock: T) -> Self {
        Offsets::new(vec![datablock])
    }
}
impl<T: Datablock + 'static> FieldValues for Offsets<T> {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        LONG::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor) -> Box<AllocatedFieldValues> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            // If there is just one block, the position will point directly at it.
            // As such, the offsets vector will be kept empty.
            let offsets = Vec::new();
            let block_size = self.data.get(0).unwrap().size(); // Data has size of 1

            // Internally allocate an extra byte if size is odd.
            // This guarantes that the next element will
            // begin on a word-boundary.
            c.allocate(
                if block_size%2 == 0 {
                    block_size
                } else {
                    block_size+1
                }
            );
            
            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: self.data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());

            for block in self.data.iter() {
                offsets.push(LONG(c.allocated_bytes()));
                c.allocate(
                    if block.size()%2 == 0 {
                        block.size()
                    } else {
                        block.size()+1
                    }
                );
            }

            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: self.data,
            })
        }
    }   
}

/// Allocated form of `Offsets`
struct AllocatedOffsets<T: Datablock> {
    position: Option<u32>,
    offsets: Vec<LONG>,
    data: Vec<T>,
}
impl<T: Datablock> AllocatedFieldValues for AllocatedOffsets<T> {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        LONG::size() * self.count()
    }

    fn position(&self) -> Option<u32> {
        self.position
    }

    fn type_id(&self) -> u16 {
        LONG::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let Self { data, offsets, ..} = unboxed;
        for offset in offsets {
            offset.write_to(file)?;
        }
        for block in data {
            let file_initial = file.written_bytes();
            let block_size = block.size();
            block.write_to(file)?;
            let mut written_size = file.written_bytes - file_initial;
            // Internally write an extra byte if size is odd.
            // This guarantes that the next element will
            // begin on a word-boundary.
            if written_size%2 == 1 { file.write_arbitrary_byte()? }
            if written_size != block_size {
                panic!(
                    "The number of bytes allocated by the Datablock ({}) is different from the number of bytes written to the file ({}).", 
                    block_size, written_size
                )
            }
        }
        
        Ok(())
    }
}

/// [`Datablock`] that consists of a list of bytes.
/// 
/// It is possible to store any block of data in a `ByteBlock`,
/// but that would require to know the [`Endianness`] of the file
/// beforehand, so the bytes are written in the correct order.
/// 
/// Using a [`Datablock`], on the other hand, allows to make use
/// of the functionality of an [`EndianFile`], so the data can be
/// written without worrying about the endianness.
/// 
/// [`Datablock`]: trait.Datablock.html
/// [`EndianFile`]: struct.EndianFile.html
/// [`Endianness`]: enum.Endianness.html
pub struct ByteBlock(pub Vec<u8>);
impl ByteBlock {
    /// Constructs an [`Offsets`] of `ByteBlock`s from a vector of
    /// vectors of bytes.
    /// 
    /// Each vector of bytes represents one `ByteBlock`.
    /// 
    /// [`Offsets`]: struct.Offsets.html
    pub fn offsets(blocks: Vec<Vec<u8>>) -> Offsets<ByteBlock> {
        Offsets::new(blocks.into_iter().map(|block| ByteBlock(block)).collect())
    }

    /// Constructs an [`Offsets`] from a vector of bytes.
    /// 
    /// This vector of bytes represents a single `ByteBlock`.
    /// 
    /// [`Offsets`]: struct.Offsets.html
    pub fn single(block: Vec<u8>) -> Offsets<ByteBlock> {
        ByteBlock::offsets(vec![block])
    }
}
impl Datablock for ByteBlock {
    fn size(&self) -> u32 {
        self.0.len() as u32
    }
    
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        for byte in self.0 {
            file.write_u8(byte)?;
        }
        Ok(())
    }
}

/// A list of values of any given [`TiffType`].
/// 
/// [`TiffType`]: tiff_type/trait.TiffType.html
pub struct TiffTypeValues<T: TiffType> {
    values: Vec<T>,
}
impl<T: TiffType + 'static> TiffTypeValues<T> {
    /// Creates a new instance of `TiffTypeValues` from a vector
    /// of instances of any given [`TiffType`].
    /// 
    /// [`TiffType`]: tiff_type/trait.TiffType.html
    pub fn new(values: Vec<T>) -> Self {
        if values.len() == 0 {
            panic!("Cannot create an empty instance of TiffTypeValues")
        }
        TiffTypeValues {
            values
        }
    }
}
impl<T: TiffType + 'static> FieldValues for TiffTypeValues<T> {
    fn count(&self) -> u32 {
        self.values.len() as u32
    }

    fn size(&self) -> u32 {
        T::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor) -> Box<AllocatedFieldValues> {
        let position = if self.size() <= 4 {
            None
        } else {
            // If the entry size is odd, it will need to allocate an extra byte
            // so that offsets continue to respect the word boundary
            let size = self.size() + self.size()%2;
            let pos = c.allocated_bytes();
            c.allocate(size);
            Some(pos)
        };
        
        Box::new(AllocatedTiffTypeValues {
            position,
            values: self.values,
        })
    }

}

/// Allocated form of `TiffTypeValues`
struct AllocatedTiffTypeValues<T: TiffType> {
    position: Option<u32>,
    values: Vec<T>,
}
impl<T: TiffType> AllocatedFieldValues for AllocatedTiffTypeValues<T> {
    fn count(&self) -> u32 {
        self.values.len() as u32
    }

    fn size(&self) -> u32 {
        T::size() * self.count()
    }

    fn position(&self) -> Option<u32> {
        self.position
    }

    fn type_id(&self) -> u16 {
        T::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let size = self.size();
        for value in self.values {
            let file_initial = file.written_bytes();
            value.write_to(file)?;
            let mut written_size = file.written_bytes - file_initial;
            if written_size != T::size() {
                panic!(
                    "The size indicated ({}) is different from the number of bytes the type has written to the file ({}).", 
                    T::size(), written_size
                )
            }
        }
       
        if size%2 == 1 && size > 4 {
            file.write_arbitrary_byte()?;
        }
        Ok(())
    }
}