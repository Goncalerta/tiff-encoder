use std::io;

use super::{AllocatedFieldValues, FieldValues};
use crate::tiff_type::{TiffType, LONG};
use crate::write::{Cursor, EndianFile};

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
/// # Examples
///
/// Creating a DataBlock for `Vec<u32>`:
/// ```
/// use std::io;
/// use tiff_encoder::*;
/// // Create a block that wraps the u32 data.
/// struct U32Block(Vec<u32>);
/// // Implement datablock functions
/// impl Datablock for U32Block {
///     fn size(&self) -> u32 {
///         // Each u32 occupies 4 bytes.
///         self.0.len() as u32 * 4
///     }
///     fn write_to(self, file: &mut write::EndianFile) -> io::Result<()> {
///         for val in self.0 {
///             file.write_u32(val)?
///         }
///         Ok(())
///     }
/// }
/// // (Optional) implement some convenient functions to construct Offsets
/// impl U32Block {
///     // Construct an Offsets to multiple U32Block
///     pub fn offsets(blocks: Vec<Vec<u32>>) -> Offsets<Self> {
///         Offsets::new(blocks.into_iter().map(|block| U32Block(block)).collect())
///     }
///     // Construct an Offsets to a single U32Block
///     pub fn single(block: Vec<u32>) -> Offsets<Self> {
///         U32Block::offsets(vec![block])
///     }
/// }
///
/// // A vector holding arbitrary u32 data.
/// // This is the data we want to store in the U32Block.
/// let data_32bits: Vec<u32> = vec![0; 65536];
///
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = U32Block::single(data_32bits);
/// ```
///
/// [`ByteBlock`]: struct.ByteBlock.html
/// [`Endianness`]: enum.Endianness.html
/// [`EndianFile`]: struct.EndianFile.html
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
        Offsets { data: datablocks }
    }

    /// Creates a new `Offsets` instance from a single [`Datablock`].
    ///
    /// [`Datablock`]: trait.Datablock.html
    pub fn single(datablock: T) -> Self {
        Offsets::new(vec![datablock])
    }
}
impl<T: Datablock + 'static> FieldValues for Offsets<T> {
    #[doc(hidden)]
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    #[doc(hidden)]
    fn size(&self) -> u32 {
        LONG::size() * self.count()
    }

    #[doc(hidden)]
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
            c.allocate(if block_size % 2 == 0 {
                block_size
            } else {
                block_size + 1
            });

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
                c.allocate(if block.size() % 2 == 0 {
                    block.size()
                } else {
                    block.size() + 1
                });
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
        let Self { data, offsets, .. } = unboxed;
        for offset in offsets {
            offset.write_to(file)?;
        }
        for block in data {
            let file_initial = file.written_bytes();
            let block_size = block.size();
            block.write_to(file)?;
            let written_size = file.written_bytes() - file_initial;
            // Internally write an extra byte if size is odd.
            // This guarantes that the next element will
            // begin on a word-boundary.
            if written_size % 2 == 1 {
                file.write_arbitrary_byte()?
            }
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
/// # Examples
///
/// Creating a ByteBlock from a `Vec<u8>`:
/// ```
/// use tiff_encoder::*;
///
/// // A vector holding arbitrary u8 data.
/// // This is the data we want to store as a Byteblock.
/// let data_8bits: Vec<u8> = vec![0; 65536];
///
/// // Create an Offsets of a single Byteblock from the buffer.
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = ByteBlock::single(data_8bits);
/// ```
///
/// Creating a ByteBlock from a `Vec<u32>`:
/// ``` extern crate byteorder;
/// // Crate byteorder will be used to write 32-bit information in a 8-bit buffer.
/// use byteorder::io::WriteBytesExt;
///
/// use tiff_encoder::*;
///
///
/// // A vector holding arbitrary u32 data.
/// // This is the data we want to store as a Byteblock.
/// let data_32bits: Vec<u32> = vec![0; 65536];
///
/// // First, let's store the data in a u8 buffer.
/// let mut image_bytes = Vec::with_capacity(262144); // 65536*4 (each u32 has a size of 4 bytes)
/// for val in data_32bits {
///     // A little endian TIFF file is assumed in this example.
///     image_bytes.write_u32::<LittleEndian>(val).unwrap();
/// }
///
/// // Create an Offsets of a single Byteblock from the buffer.
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = ByteBlock::single(image_bytes);
/// ```
///
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
        file.write_all_u8(&self.0)?;
        Ok(())
    }
}
