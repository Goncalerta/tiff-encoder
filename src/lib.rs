//! A crate for encoding TIFF files. (WIP)

extern crate byteorder;

use std::fs;
use std::io;
use byteorder::{WriteBytesExt, LittleEndian, BigEndian};
use std::collections::BTreeMap;

pub mod tiff_type;
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
    /// Returns the u16 value that represents the given endianness in a TIF Header.
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
}
impl EndianFile {
    /// Writes a u8 to the file.
    fn write_u8(&mut self, n: u8) -> io::Result<()> {
        self.file.write_u8(n)
    }

    /// Writes a u16 to the file.
    fn write_u16(&mut self, n: u16) -> io::Result<()> {
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
    fn write_u32(&mut self, n: u32) -> io::Result<()> {
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
    fn write_i8(&mut self, n: i8) -> io::Result<()> {
        self.file.write_i8(n)
    }

    /// Writes a i16 to the file.
    fn write_i16(&mut self, n: i16) -> io::Result<()> {
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
    fn write_i32(&mut self, n: i32) -> io::Result<()> {
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
    fn write_f32(&mut self, n: f32) -> io::Result<()> {
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
    fn write_f64(&mut self, n: f64) -> io::Result<()> {
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
    /// doesn't hold any information.
    fn write_arbitrary_byte(&mut self) -> io::Result<()> {
        self.file.write_u8(0)
    }
}

/// Used during the allocation phase of the process of creating
/// a TIFF file.
/// 
/// Holds the number of bytes that were allocated, in order to
/// calculate the needed offsets.
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
    pub fn allocate(&mut self, n: u32) {
        self.0 = match self.0.checked_add(n) {
            Some(val) => val,
            None => panic!("Attempted to write a TIFF file bigger than 2**32 bytes."),
        };
    }

    /// Returns the number of already allocated bytes.
    pub fn allocated_bytes(&self) -> u32 {
        self.0
    }
}

/// Representation of a Tagged Image File.
pub struct TiffFile {
    header: TiffHeader,
    ifds: IfdChain,
}

impl TiffFile {

    /// Creates a new `TiffFile` from an [`IfdChain`].
    /// 
    /// By default, a `TiffFile` is little-endian and has 42 as the magic number.
    /// If you want to change this for some reason, consider chaining this function wih
    /// [`with_endianness`] or [`with_magic_number`], respectively.
    /// 
    /// # Examples
    /// 
    /// Creating the simplest `TiffFile`: a single [`Ifd`] with only one entry.
    /// ```
    /// let tiff_file = TiffFile::new() (
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// );
    /// ```
    /// [`Ifd`]: struct.Ifd.html
    /// [`IfdChain`]: struct.IfdChain.html
    /// [`with_endianness`]: #method.with_endianness
    /// [`with_magic_number`]: #method.with_magic_number
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
    /// As this method returns `Self`, it can be chained with others when
    /// building a `TiffFile`.
    /// ```
    /// let tiff_file = TiffFile::new() (
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// ).with_endianness(Endianness::MM).with_magic_number(43);
    /// ```
    pub fn with_endianness(mut self, endian: Endianness) -> Self {
        self.header.byte_order = endian;
        self
    }

    /// Returns the same `TiffFile`, but with the specified magic number.
    /// 
    /// # Examples
    /// 
    /// As this method returns `Self`, it can be chained with others when
    /// building a `TiffFile`.
    /// ```
    /// let tiff_file = TiffFile::new() (
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// ).with_magic_number(43).with_endianness(Endianness::MM);
    /// ```
    /// 
    /// # Panics
    /// 
    /// The magic number of a `TiffFile` is always at least 42. Attempting
    /// to create a TiffFile with a smaller value will panic.
    pub fn  with_magic_number(mut self, magic_number: u16) -> Self {
        if magic_number < 42 { panic!("The magic number of a TiffFile cannot be less than 42.") }
        self.header.magic_number = magic_number;
        self
    }

    /// Writes the `TiffFile`, creating a new file at the given path.
    /// 
    /// Doing so consumes the `TiffFile`. Returns the new file wrapped in
    /// an `io::Result`.
    /// 
    /// # Examples
    /// 
    /// Note that in this example, `file` is a `fs::File`, not a `TiffFile`.
    /// ```
    /// let file = TiffFile::new() (
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE::single(0))
    ///         .single()
    /// ).write_to("file.tif").unwrap();
    /// ```
    pub fn write_to(self, file_path: &str) -> io::Result<fs::File> {
        let file = fs::File::create(file_path)?;
        // Writing to a file is comprised of two phases: "Allocating Phase" 
        // and "Writting Phase". During the first, all the components of the
        // TiffFile allocate their space and become aware of the offsets they
        // need to know. In the "Writting Phase", the components actually 
        // write their information to the file they've been allocated to.
        self.allocate(file).write()
    }

    /// Allocates all its components to the given file, transforming
    /// itself into an `AllocatedTiffFile`.
    fn allocate(self, file: fs::File) -> AllocatedTiffFile {
        let mut c = Cursor::new();
        let header = self.header.allocate(&mut c);
        let ifds = self.ifds.allocate(&mut c);
        let file = EndianFile {
            file,
            byte_order: header.byte_order,
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
}
impl Datablock for IfdChain {
    #[doc(hidden)]
    type Allocated = AllocatedIfdChain;

    /// Allocates every `Ifd` in the chain, moving the given `Cursor` forwards.
    /// 
    /// Calling this will transform `self` into an `AllocatedIfdChain`.
    #[doc(hidden)]
    fn allocate(self, c: &mut Cursor) -> AllocatedIfdChain {
        let len = self.0.len();
        let mut ifds = Vec::with_capacity(len);
        for (index, ifd) in self.0.into_iter().enumerate() {
            ifds.push(ifd.allocate(c, index+1 == len));
        }
        AllocatedIfdChain(ifds)
    }

    /// Returns the size of this IfdChain, that is,
    /// 
    /// the sum of the sizes of all the `IFD`s it contains. 
    #[doc(hidden)]
    fn size(&self) -> u32 {
        self.0.iter().map(|ifd| ifd.size()).sum()
    }
      
}
//// An `IfdChain` that called `allocate(&mut Cursor)` and is
/// ready to write to a file.
#[doc(hidden)]
pub struct AllocatedIfdChain(Vec<AllocatedIfd>);
impl AllocatedDatablock for AllocatedIfdChain {
    /// Returns the size of this IfdChain, that is,
    /// 
    /// the sum of the sizes of all the `IFD`s it contains. 
    fn size(&self) -> u32 {
        self.0.iter().map(|ifd| ifd.size()).sum()
    }

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
    /// [`with_entry(FielTag, FieldValues)`] in order to build a valid `Ifd`.
    /// 
    /// [`with_entry(FielTag, FieldValues)`]: #method.with_entry
    pub fn new() -> Ifd {
        Ifd {
            entries: BTreeMap::new(),
        }
    }

    /// Returns the same `Ifd`, but adding the given pair of Tag and Values.
    /// 
    /// Because of returning the `Ifd`, it is possible to chain this method.
    /// 
    /// # Examples
    /// 
    /// Creating a [`TiffFile`] with some arbitrary entries.
    /// 
    /// Note in which entries are added is irrelevant. Internally, the
    /// `Ifd` will arrange them automatically by ascending order of tags, as
    /// specified by the TIFF specification.
    /// 
    /// ```
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
    /// [`TiffFile`]: struct.TiffFile.html
    pub fn with_entry<T: FieldValues + 'static>(mut self, tag: FieldTag, value: T) -> Self {
        if self.entries.insert(tag, Box::new(value)).is_some() {
            panic!("Tried to add the same tag twice.");
        }
        self
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
    pub fn entry_count(&self) -> u32 {
        self.entries.len() as u32
    }

    /// Returns the number of bytes occupied by this `Ifd` in its binary form.
    /// 
    /// Note that this only includes the IFD itself, not the values associated
    /// with it that don't fit in their entry.
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
    /// Returns the number of bytes occupied by this `Ifd` in its binary form.
    /// 
    /// Note that this only includes the IFD itself, not the values associated
    /// with it that don't fit in their entry.
    fn size(&self) -> u32 {
        self.entries.len() as u32 * 12 + 6
    }

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
pub type FieldTag = u16;

/// Seals FieldValues, so that it can only be implemented inside
/// the crate. There are only two types of FieldValues:
/// `Offsets` and `TiffTypeValues`.
mod private {
    pub trait Sealed {}
    impl<T: super::Datablock> Sealed for super::Offsets<T> {}
    impl<T: super::TiffType> Sealed for super::TiffTypeValues<T> {}
}

/// The values contained or pointed at by an IFD Field.
/// 
/// There are two big groups of `FieldValues`: [`TiffTypeValues`]
/// and [`Offsets`]. The first represents a list of values of any
/// given [`TiffType`]. The second represents a list of [`LONG`]
/// values, each pointing to a specific [`Datablock`].
/// 
/// It is not possible to implement this trait manually outside of
/// this crate.
/// 
/// [`TiffTypeValues`]: struct.TiffTypeValues.html
/// [`Offsets`]: struct.Offsets.html
/// [`TiffType`]: tiff_types/trait.TiffType.html
/// [`LONG`]:tiff_types/struct.LONG.html
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

/// Represents a block of data in the file pointed to by a field value, but
/// that isn't part of the field itself.
/// 
/// This includes, for example, subIFDs and image strips.
/// 
/// In most cases, it is simpler to implement [`SimpleDatablock`] instead,
/// which will automatically implement both `Datablock` and its allocated form,
/// [`AllocatedDatablock`]. Implementing `Datablock` directly is only useful
/// if there is need to track the position of the block in the file (in order
/// to write offsets, for example).
/// 
/// # Important
/// 
/// Be careful to respect all the rules specified in each of its methods when
/// implementing `Datablock`. A poor implementation that does not respect those
/// rules may compromise the whole resulting TIFF file, making it invalid.
/// 
/// [`SimpleDatablock`]: trait.SimpleDatablock
/// [`AllocatedDatablock`]: trait.AllocatedDatablock
pub trait Datablock {
    /// The allocated form of this `Datablock`.
    /// 
    /// It is valid for a structure to be both its normal and allocated form,
    /// as long as it doens't need to store any different information after
    /// allocation. In that case, `type Allocated = Self`.
    type Allocated: AllocatedDatablock;

    /// The number of bytes occupied by this `Datablock`.
    /// 
    /// # Important
    /// 
    /// This value must not change between the allocation and writing to 
    /// the file. The number of allocated bytes to the [`Cursor`] in 
    /// [`allocate(self, &mut Cursor)`] and the number of written bytes 
    /// to the [`EndianFile`] in [`write_to(self, &mut EndianFile)`] must
    /// be the same value returned by this function.
    /// 
    /// Failing to meet the specifications in the previous paragraph may
    /// result in the whole resulting TIFF file becoming invalid.
    /// 
    /// [`Cursor`]: struct.Cursor.html
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`allocate(self, &mut Cursor)`]: #method.allocate
    /// [`write_to(self, &mut EndianFile)`]: trait.AllocatedDatablock.html#method.write_to
    fn size(&self) -> u32;

    /// Allocates this `Datablock`, moving the [`Cursor`] forwards exactly
    /// the same number of bytes as returned by [`size(&self)`]. Returns its
    /// allocated form, [`Self::Allocated`].
    /// 
    /// # Important
    /// 
    /// Failing to allocate the exact same number of bytes as indicated in
    /// [`size(&self)`] may compromise the whole TIFF file.
    /// 
    /// [`Cursor`]: struct.Cursor.html
    /// [`size(&self)`]: #method.size
    /// [`Self::Allocated`]: #associatedtype.Allocated
    fn allocate(self, c: &mut Cursor) -> Self::Allocated;
}

/// Represents a [`Datablock`] that already called [`allocate(self, &mut Cursor)`].
/// 
/// # Important
/// 
/// Be careful to respect all the rules specified in each of its methods when
/// implementing `AllocatedDatablock`. A poor implementation that does not respect 
/// those rules may compromise the whole resulting TIFF file, making it invalid.
/// 
/// [`Datablock`]: trait.Datablock
/// [`allocate(self, &mut Cursor)`]: trait.Datablock#method.allocate
pub trait AllocatedDatablock {
    /// The number of bytes occupied by this `AllocatedDatablock`.
    /// 
    /// # Important
    /// 
    /// This value must not change between the allocation and writing to 
    /// the file. The number of allocated bytes to the [`Cursor`] in 
    /// [`allocate(self, &mut Cursor)`] and the number of written bytes 
    /// to the [`EndianFile`] in [`write_to(self, &mut EndianFile)`] must
    /// be the same value returned by this function.
    /// 
    /// Failing to meet the specifications in the previous paragraph may
    /// result in the whole resulting TIFF file becoming invalid.
    /// 
    /// [`Cursor`]: struct.Cursor.html
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`allocate(self, &mut Cursor)`]: trait.Datablock.html#method.allocate
    /// [`write_to(self, &mut EndianFile)`]: #method.write_to
    fn size(&self) -> u32;

    /// Writes this `AllocatedDatablock` to an [`EndianFile`]. The number
    /// of bytes written must be exactly same number as returned by [`size(&self)`].
    /// 
    /// # Important
    /// 
    /// Failing to write the exact same number of bytes as indicated in
    /// [`size(&self)`] may compromise the whole TIFF file.
    /// 
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`size(&self)`]: #method.size
    fn write_to(self, file: &mut EndianFile) -> io::Result<()>;
}

/// A trait that conveniently implements automatically [`Datablock`] and
/// [`AllocatedDatablock`].
/// 
/// In the vast majority of cases, the `Datablock` doesn't need to be aware of 
/// its position in the file. In those cases, implementing this trait is
/// preferable in relation to directly implementing the two mentioned earlier.
/// 
/// # Important
/// 
/// Be careful to respect all the rules specified in each of its methods when
/// implementing `Datablock`. A poor implementation that does not respect those
/// rules may compromise the whole resulting TIFF file, making it invalid.
/// 
/// [`Datablock`]: trait.Datablock
/// [`AllocatedDatablock`]: trait.AllocatedDatablock
pub trait SimpleDatablock {
    /// The number of bytes occupied by this `Datablock`.
    /// 
    /// # Important
    /// 
    /// The number of written bytes to the [`EndianFile`] in 
    /// [`write_to(self, &mut EndianFile)`] must be the same value returned 
    /// by this function.
    /// 
    /// Failing to meet that specification may result in the whole resulting 
    /// TIFF file becoming invalid.
    /// 
    /// [`EndianFile`]; struct.EndianFile.html
    /// [`write_to(self, &mut EndianFile)`]: #method.write_to
    fn size(&self) -> u32;

    /// Writes this `Datablock` to an [`EndianFile`]. The number of bytes 
    /// written must be exactly same number as returned by [`size(&self)`].
    /// 
    /// # Important
    /// 
    /// Failing to write the exact same number of bytes as indicated in
    /// [`size(&self)`] may compromise the whole TIFF file.
    /// 
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`size(&self)`]: #method.size
    fn write_to(self, file: &mut EndianFile) -> io::Result<()>;
}
impl<T: SimpleDatablock> Datablock for T {
    type Allocated = Self;
    fn size(&self) -> u32 {
        SimpleDatablock::size(self)
    }
    fn allocate(self, c: &mut Cursor) -> Self::Allocated {
        c.allocate(SimpleDatablock::size(&self));
        self
    }
}
impl<T: SimpleDatablock> AllocatedDatablock for T {
    fn size(&self) -> u32 {
        SimpleDatablock::size(self)
    }
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        SimpleDatablock::write_to(self, file)
    }
}

/// Represents a list of [`LONG`] values, each pointing to a specific 
/// [`Datablock`].
/// 
/// This structure owns the list of Datablocks instead, so the user
/// doesn't have to deal with the offsets in the file. It is responsible
/// for allocating and writing both the offsets and the blocks of data.
/// 
/// [`LONG`]:tiff_types/struct.LONG.html
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
            let block = self.data.into_iter().next().unwrap(); // Data has size of 1
            let block_has_odd_size = block.size()%2 == 1;
            let allocated_data = vec![block.allocate(c)];
            if block_has_odd_size { c.allocate(1) }
            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: allocated_data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());
            let mut allocated_data = Vec::with_capacity(self.data.len());

            for block in self.data {
                offsets.push(LONG(c.allocated_bytes()));
                let block_has_odd_size = block.size()%2 == 1;
                allocated_data.push(block.allocate(c));
                if block_has_odd_size { c.allocate(1) }
            }

            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: allocated_data,
            })
        }
    }
}

/// Allocated form of `Offsets`
struct AllocatedOffsets<T: AllocatedDatablock> {
    position: Option<u32>,
    offsets: Vec<LONG>,
    data: Vec<T>,
}
impl<T: AllocatedDatablock> AllocatedFieldValues for AllocatedOffsets<T> {
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
        let Self { data, offsets,..} = unboxed;
        for offset in offsets {
            offset.write_to(file)?;
        }
        for block in data {
            let block_has_odd_size = block.size()%2 == 1;
            block.write_to(file)?;
            if block_has_odd_size { file.write_arbitrary_byte()? }
        }
        
        Ok(())
    }
}

/// [`Datablock`] that consists of a list of bytes.
/// 
/// [`Datablock`]: trait.Datablock
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
}
impl SimpleDatablock for ByteBlock {
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

/// Represents a list of values of any given [`TiffType`].
/// 
/// [`TiffType`] tiff_type/trait.TiffType.html
pub struct TiffTypeValues<T: TiffType> {
    values: Vec<T>,
}
impl<T: TiffType + 'static> TiffTypeValues<T> {
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
            value.write_to(file)?;
        }
       
        if size%2 == 1 && size > 4 {
            file.write_arbitrary_byte()?;
        }
        Ok(())
    }
}