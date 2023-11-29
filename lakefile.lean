import Lake
open Lake DSL

package «concu» where
  -- add package configuration options here

--require aesop from git "https://github.com/JLimperg/aesop"
require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «Concu» where
  -- add library configuration options here
