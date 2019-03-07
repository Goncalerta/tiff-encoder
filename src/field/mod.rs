use std::io;

use crate::write::{Cursor, EndianFile};

mod datablock_value;
mod ifd_value;
mod tiff_type_value;

pub use self::datablock_value::*;
pub use self::ifd_value::*;
pub use self::tiff_type_value::*;

/// 16-bit identifier of a field entry.
///
/// The module [`tag`] has some constants for commonly used
/// `FieldTag`s.
///
/// [`tag`]: ./tag/index.html
pub type FieldTag = u16;

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

/// Seals FieldValues, so that it can only be implemented inside
/// the crate. There are only three types of FieldValues:
/// `Offsets` to datablocks, `OffsetsToIfds` and `TiffTypeValues`.
mod private {
    use crate::tiff_type::TiffType;

    pub trait Sealed {}
    impl<T: super::Datablock> Sealed for super::Offsets<T> {}
    impl<T: TiffType> Sealed for super::TiffTypeValues<T> {}
    impl Sealed for super::OffsetsToIfds {}
}
