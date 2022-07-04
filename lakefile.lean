import Lake
open Lake DSL

package Unicode

@[defaultTarget]
lean_lib Unicode

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"ecd37441047e490ff2ad339e16f45bb8b58591bd"

