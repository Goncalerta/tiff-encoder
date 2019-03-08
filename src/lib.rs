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
//!         .with_entry(tag::PhotometricInterpretation, SHORT![1]) // Black is zero
//!         .with_entry(tag::Compression, SHORT![1]) // No compression
//!
//!         .with_entry(tag::ImageLength, LONG![256])
//!         .with_entry(tag::ImageWidth, LONG![256])
//!
//!         .with_entry(tag::ResolutionUnit, SHORT![1]) // No resolution unit
//!         .with_entry(tag::XResolution, RATIONAL![(1, 1)])
//!         .with_entry(tag::YResolution, RATIONAL![(1, 1)])
//!
//!         .with_entry(tag::RowsPerStrip, LONG![256]) // One strip for the whole image
//!         .with_entry(tag::StripByteCounts, LONG![8192])
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

pub mod ifd;
pub mod write;

mod file;
pub use file::TiffFile;
