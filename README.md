# Unicode.lean

Unicode related operations for Lean 4.

- [x] Unicode General Category
- [ ] TODO

## Installation

In your lakefile.lean add `Unicode.lean` as dependency:

```lean
package foo {
  dependencies := #[
    {
      name := `Unicode
      src := Source.git "https://github.com/xubaiw/Unicode.lean" "<hash>"
    }
  ]
}
```

## Usage

The following example shows how to get general category propert of a character:

```lean
import Unicode.General.GeneralCategory
open Unicode

#eval getGeneralCategory 'a' -- Ll, lowercase letter
#eval getGeneralCategory '←' -- Sm, math symbol
#eval getGeneralCategory '-' -- Pd, dash punctuation
#eval getGeneralCategory $ Char.mk 0x10ead (by decide) -- Pd, dash punctuation
```