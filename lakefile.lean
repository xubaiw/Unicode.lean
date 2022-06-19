import Lake
open Lake DSL

package Unicode

@[defaultTarget]
lean_lib Unicode

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"58f072fdbfd5dd77c98d8393a489ed3eff383ac8"

