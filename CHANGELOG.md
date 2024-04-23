# Revision history for demangler

## 1.3.2.0 -- 2023.04.22

* Fix handling of discriminators.
* Add handling for UnnamedTypeName unqualified names.
* Fix parsing of primary expressions in template parameters.
* Fully support DeclType elements.
* More complete implementation of function params.
* Fix parsing of reference qualifiers
* Suppress function argument output for template arguments.
* Allow extraction of function names with unnamed-type elements.
* Convert full ClassUnionStructEnum name to a substitutable prefix.
* Suppress any visible indication of empty template argument packs.
* Add C11 argument pack expansion support with template argument packs.
* Add support for pointer-to-member-type elements.
* Proper UnscopedName parsing for template parameters.
* Fixed order of CV qualifier parsing.

## 1.3.1.0 -- 2023.11.12

* Added support for demangling expressions.

## 1.3.0.0 -- 2023.11.09

* Added `functionName` accessor to retrieve the name portions only of a function
  (in reverse heirarchical order).

## 1.2.0.0 -- 2023.10.29

* Updated support for local names.

## 1.1.0.0 -- 2023.10.23

* Added support for `ABI_Tags` on `SourceName`.
* Added support for `Array` types with bounds.
* Added support for `ModuleName` on `UnqualifiedName`.
* Explicit `SourceName` in API and used where appropriate (breaking change).
* Updated `Sayable` to use `sayableSubConstraints`.

## 1.0.0.0 -- 2023.10.20

* Initial release.

## 0.2.0.0 -- 2023.10.18

* Parity with origin tests.

## 0.1.0.0 -- 2023-10-15

* Initial version.
