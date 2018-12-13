# Change Log

## 0.2.1 - 2018-12-13

### Fix

* If writing the file to a path that doesn't exist, automatically create all missing directories.

## 0.2.0 - 2018-12-12

### Feature

* `TiffFile::write_to` can now be used with any type implementing `AsRef<Path>`, instead of being limited to `&str`.

## 0.1.2 - 2018-12-01

### Performance

* Increase performance when writing large files.

### Documentation

* Minor tweaks.
* Fix failed documentation tests.

## 0.1.1 - 2018-10-10

### Documentation

* Improved documentation, adding examples to Datablock and Byteblock.

* Deleted github pages with documentation, as it can be accessed from [docs.rs](https://docs.rs/tiff-encoder).

## 0.1.0 - 2018-10-04

* Initial release