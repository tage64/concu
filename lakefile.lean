import Lake
open Lake DSL

package «concu» where
  -- add package configuration options here

require aesop from git "https://github.com/JLimperg/aesop"

@[default_target]
lean_lib «Concu» where
  -- add library configuration options here
