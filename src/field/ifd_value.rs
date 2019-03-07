use std::io;

use super::{AllocatedFieldValues, FieldValues};
use crate::tiff_type::{TiffType, IFD};
use crate::write::{Cursor, EndianFile};
use crate::{AllocatedIfdChain, IfdChain};

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
