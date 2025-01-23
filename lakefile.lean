import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package "nat2" where
  -- add package configuration options here

lean_lib «Nat2» where
  -- add library configuration options here

@[default_target]
lean_exe "nat2" where
  root := `Main
