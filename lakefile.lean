import Lake
open Lake DSL

package «parsing» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


require batteries_extra from git
  "https://github.com/pthomas505/batteries_extra.git" @ "main"


@[default_target]
lean_lib «Parsing» where
  -- add any library configuration options here
