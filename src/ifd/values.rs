//! The values contained or pointed at by an IFD Field.
//!
//! There are three groups of [`FieldValues`]: [`TiffTypeValues`],
//! [`Offsets`] and [`OffsetsToIfds`]. The first represents a list
//! of values of any given [`TiffType`]. The second represents a
//! list of [`LONG`] values, each pointing to a specific [`Datablock`].
//! The third represents a list of [`IFD`] values, each pointing to
//! an [`Ifd`].
//!
//! [`FieldValues`]: trait.FieldValues.html
//! [`TiffTypeValues`]: struct.TiffTypeValues.html
//! [`Offsets`]: struct.Offsets.html
//! [`OffsetsToIfds`]: struct.OffsetsToIfds.html
//! [`TiffType`]: ../types/trait.TiffType.html
//! [`LONG`]: ../types/struct.LONG.html
//! [`IFD`]: ../types/struct.IFD.html
//! [`Datablock`]: ../../write/trait.Datablock.html

use std::io;

use crate::ifd::types::{TiffType, IFD, LONG};
use crate::ifd::{AllocatedIfdChain, IfdChain};
use crate::write::{Cursor, Datablock, EndianFile};

/// The values contained or pointed at by an IFD Field.
///
/// There are three groups of `FieldValues`: [`TiffTypeValues`],
/// [`Offsets`] and [`OffsetsToIfds`]. The first represents a list
/// of values of any given [`TiffType`]. The second represents a
/// list of [`LONG`] values, each pointing to a specific [`Datablock`].
/// The third represents a list of [`IFD`] values, each pointing to
/// an [`Ifd`].
///
/// This trait is sealed. It is not possible to implement it outside
/// this crate.
///
/// [`TiffTypeValues`]: struct.TiffTypeValues.html
/// [`Offsets`]: struct.Offsets.html
/// [`OffsetsToIfds`]: struct.OffsetsToIfds.html
/// [`TiffType`]: ../types/trait.TiffType.html
/// [`LONG`]: ../types/struct.LONG.html
/// [`IFD`]: ../types/struct.IFD.html
/// [`Datablock`]: ../../write/trait.Datablock.html
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

/// Seals FieldValues, so that it can only be implemented inside
/// the crate. There are only three types of FieldValues:
/// `Offsets` to datablocks, `OffsetsToIfds` and `TiffTypeValues`.
mod private {
    pub trait Sealed {}
    impl<T: super::Datablock> Sealed for super::Offsets<T> {}
    impl<T: super::TiffType> Sealed for super::TiffTypeValues<T> {}
    impl Sealed for super::OffsetsToIfds {}
}

/// A list of [`LONG`] values, each pointing to a specific
/// [`Datablock`].
///
/// This structure owns the list of Datablocks instead, so the user
/// doesn't have to deal with the offsets in the file. It is responsible
/// for writing both the offsets and the blocks of data.
///
/// [`LONG`]: ../types/struct.LONG.html
/// [`Datablock`]: ../../write/trait.Datablock.html
pub struct Offsets<T: Datablock> {
    pub data: Vec<T>,
}
impl<T: Datablock + 'static> Offsets<T> {
    /// Creates a new `Offsets` instance from a vector of [`Datablock`]s.
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
    pub fn new(datablocks: Vec<T>) -> Self {
        Offsets { data: datablocks }
    }

    /// Creates a new `Offsets` instance from a single [`Datablock`].
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
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

/// A list of values of any given [`TiffType`].
///
/// [`TiffType`]: ../types/trait.TiffType.html
#[derive(Debug, PartialEq)]
pub struct TiffTypeValues<T: TiffType> {
    values: Vec<T>,
}
impl<T: TiffType + 'static> TiffTypeValues<T> {
    /// Creates a new instance of `TiffTypeValues` from a vector
    /// of instances of any given [`TiffType`].
    ///
    /// [`TiffType`]: ../types/trait.TiffType.html
    pub fn new(values: Vec<T>) -> Self {
        if values.len() == 0 {
            panic!("Cannot create an empty instance of TiffTypeValues")
        }
        TiffTypeValues { values }
    }
}
impl<T: TiffType + 'static> FieldValues for TiffTypeValues<T> {
    #[doc(hidden)]
    fn count(&self) -> u32 {
        self.values.len() as u32
    }

    #[doc(hidden)]
    fn size(&self) -> u32 {
        T::size() * self.count()
    }

    #[doc(hidden)]
    fn allocate(self: Box<Self>, c: &mut Cursor) -> Box<AllocatedFieldValues> {
        let position = if self.size() <= 4 {
            None
        } else {
            // If the entry size is odd, it will need to allocate an extra byte
            // so that offsets continue to respect the word boundary
            let size = self.size() + self.size() % 2;
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
            let written_size = file.written_bytes() - file_initial;
            if written_size != T::size() {
                panic!(
                    "The size indicated ({}) is different from the number of bytes the type has written to the file ({}).", 
                    T::size(), written_size
                )
            }
        }

        if size % 2 == 1 && size > 4 {
            file.write_arbitrary_byte()?;
        }
        Ok(())
    }
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
/// [`LONG`]: ../types/struct.LONG.html
/// [`IFD`]: ../types/struct.IFD.html
/// [`Ifd`]: ../struct.Ifd.html
/// [`IfdChain`]: ../struct.IfdChain.html
pub struct OffsetsToIfds {
    pub data: Vec<IfdChain>,
}
impl OffsetsToIfds {
    /// Creates a new `OffsetsToIfds` instance from a vector of [`IfdChain`]s.
    ///
    /// [`IfdChain`]: ../struct.IfdChain.html
    pub fn new(ifds: Vec<IfdChain>) -> Self {
        OffsetsToIfds { data: ifds }
    }
}
impl FieldValues for OffsetsToIfds {
    #[doc(hidden)]
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    #[doc(hidden)]
    fn size(&self) -> u32 {
        IFD::size() * self.count()
    }

    #[doc(hidden)]
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
        let Self { data, offsets, .. } = unboxed;
        for offset in offsets {
            offset.write_to(file)?;
        }
        for ifd in data.into_iter() {
            ifd.write_to(file)?;
        }

        Ok(())
    }
}
