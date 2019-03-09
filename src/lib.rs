//! A crate for encoding TIFF files.
//!
//! This crate allows to create any hierarchy of IFDs and to add any
//! tags with any values to each. It does so while avoiding that
//! the user needs to worry about the position of each structure in the
//! file and to point to it with the correct offset.
//!
//! The main structure of this crate, used to actually write the TIFF
//! file, is the [`TiffFile`]. This structure writes the file in [little endian]
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
//! #[macro_use]
//! extern crate tiff_encoder;
//! use tiff_encoder::prelude::*;
//! use tiff_encoder::ifd::tags;
//!
//! # fn main() {
//! // 256*256/8 = 8192
//! // The image data will have 8192 bytes with 0 in every bit (each representing a
//! // black pixel).
//! let image_data = vec![0x00; 8192];
//!
//! TiffFile::new(
//!     Ifd::new()
//!         .with_entry(tags::PhotometricInterpretation, SHORT![1]) // Black is zero
//!         .with_entry(tags::Compression, SHORT![1]) // No compression
//!
//!         .with_entry(tags::ImageLength, LONG![256])
//!         .with_entry(tags::ImageWidth, LONG![256])
//!
//!         .with_entry(tags::ResolutionUnit, SHORT![1]) // No resolution unit
//!         .with_entry(tags::XResolution, RATIONAL![(1, 1)])
//!         .with_entry(tags::YResolution, RATIONAL![(1, 1)])
//!
//!         .with_entry(tags::RowsPerStrip, LONG![256]) // One strip for the whole image
//!         .with_entry(tags::StripByteCounts, LONG![8192])
//!         .with_entry(tags::StripOffsets, ByteBlock::single(image_data))
//!         .single() // This is the only Ifd in its IfdChain
//! ).write_to("example.tif").unwrap();
//! # }
//! ```
//!
//! [`TiffFile`]: struct.TiffFile.html
//! [little endian]: write/enum.Endianness.html#variant.II
//! [`Ifd`]: ifd/struct.Ifd.html
//! [`IfdChain`]: ifd/struct.IfdChain.html
//! [`FieldTag`]: ifd/tags/type.FieldTag.html
//! [`FieldValues`]: ifd/values/trait.FieldValues.html

extern crate byteorder;

pub mod ifd;
pub mod write;

mod file;
pub use file::TiffFile;

/// Common imports that are necessary for almost every use of the `tiff_encoder`
/// library.
///
/// # Usage
/// ```
/// use tiff_encoder::prelude::*;
/// ```
///
/// # Other common imports
///
/// The following imports, although also often used for this library, are not
/// included in the prelude to avoid polluting the user's namespace.
///
/// ```
/// use tiff_encoder::write; // Helpers to write data to the file, particularly `Datablock`
/// use tiff_encoder::ifd::tags; // Constants for common tags in IFD entries
/// ```
///
/// Note that `macro_rules!` for using [`ifd::types`] cannot (unfortunately) be re-exported
/// in the prelude. This means you'll either have to explicitely import them or use `#[macro_use]`.
///
/// ```
/// // Either
/// #[macro_use]
/// extern crate tiff_encoder;
///
/// // Or
/// use tiff_encoder::{
///     ASCII, BYTE, DOUBLE, FLOAT, LONG, RATIONAL,
///     SBYTE, SHORT, SLONG, SRATIONAL, SSHORT, UNDEFINED
/// };
///
/// # fn main() {}
/// ```
///
/// [`ifd::types`]: ../ifd/types/index.html
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::ifd::Ifd;
    #[doc(no_inline)]
    pub use crate::ifd::IfdChain;
    #[doc(no_inline)]
    pub use crate::write::ByteBlock;
    #[doc(no_inline)]
    pub use crate::TiffFile;
}
