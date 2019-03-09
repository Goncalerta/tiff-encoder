//! Module to manipulate IFDs and their entries.
//!
//! An image file directory (IFD) contains information about the image, as
//! well as pointers to the actual image data (both stored as entries).
//!
//! In a TIFF file, an IFD may point to another IFD with its last 4
//! bytes. To abstract the user of this crate from the position of each
//! structure in the file, this link between [`Ifd`]s is represented by
//! an [`IfdChain`]. Because any IFD could technically point to a next
//! one, in most functions that one would expect to input an `Ifd`, its
//! parameters actually ask for an `IfdChain`.
//!
//! [`IfdChain`]: struct.IfdChain.html
//! [`Ifd`]: struct.Ifd.html

pub mod tags;
pub mod types;
pub mod values;

mod ifd;
pub use ifd::*;
