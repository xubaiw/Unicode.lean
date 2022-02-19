# Unicode.lean

Unicode related operations for Lean 4.

- [x] Unicode General Category
- [ ] TODO

*NOTE:* As Unicode is a huge specification, it will take a long time to implement all its features. If you feel some feature is more urgent, feel free to open an issue or a pull request!

## Installation

In your lakefile.lean add `Unicode.lean` as dependency:

```lean
package foo {
  dependencies := #[{
    name := `Unicode
    src := Source.git "https://github.com/xubaiw/Unicode.lean" "main" 
  }]
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

More examples can be found in the examples folder, and the [documentation](https://xubaiw.github.io/Unicode.lean/Unicode.html) is redered through `doc-gen4`.