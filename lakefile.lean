import Lake
open Lake DSL

package «dlmst» where
  version := v!"0.1.0"
  leanOptions := #[⟨`maxHeartbeats, 1000000⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «DLMST» where
  globs := #[.andSubmodules `DLMST]
