import Lake
open Lake DSL

package «concu» where
  -- add package configuration options here
  moreLinkArgs := #["-L./.lake/packages/LeanInfer/.lake/build/lib", "-lonnxruntime", "-lctranslate2"]

--require aesop from git "https://github.com/JLimperg/aesop"
require mathlib from git "https://github.com/leanprover-community/mathlib4"
require LeanInfer from git "https://github.com/lean-dojo/LeanInfer.git" @ "v0.1.0"

@[default_target]
lean_lib «Concu» where
  -- add library configuration options here
