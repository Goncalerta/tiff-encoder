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

pub mod tag;
pub mod tiff_type;

use std::collections::BTreeMap;
use std::fs;

use std::io;
use std::path::Path;

mod field;
mod write;
pub use field::*;
pub use write::*;

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
    pub fn write_to<P: AsRef<Path>>(self, file_path: P) -> io::Result<fs::File> {
        // Create all of the file's parent components if they are missing before
        // trying to create the file itself.
        if let Some(dir) = file_path.as_ref().parent() {
            fs::create_dir_all(dir)?;
        }

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
        let file = EndianFile::new(file, header.byte_order);

        AllocatedTiffFile { header, ifds, file }
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

        Ok(self.file.into())
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
        if ifds.len() == 0 {
            panic!("Cannot create a chain without IFDs.")
        }
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
            ifds.push(ifd.allocate(c, index + 1 == len));
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
/// An image file directory (IFD) contains information about the image, as
/// well as pointers to the actual image data (both stored as entries).
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
    fn write_entry_to(
        (tag, value): (FieldTag, Box<AllocatedFieldValues>),
        file: &mut EndianFile,
    ) -> io::Result<Option<Box<AllocatedFieldValues>>> {
        file.write_u16(tag)?;
        file.write_u16(value.type_id())?;
        file.write_u32(value.count())?;

        match value.position() {
            Some(position) => {
                file.write_u32(position)?;
                Ok(Some(value))
            }
            None => {
                let size = value.size();
                value.write_to(file)?;
                for _ in 0..(4 - size) {
                    file.write_u8(0)?;
                }
                Ok(None)
            }
        }
    }
}
