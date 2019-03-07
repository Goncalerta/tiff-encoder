use std::io;

use super::{AllocatedFieldValues, FieldValues};
use crate::tiff_type::TiffType;
use crate::write::{Cursor, EndianFile};

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
