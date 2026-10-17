import Lake
open Lake DSL

package «cdcl-proof» where

@[default_target]
lean_lib «CdclProof» where
  globs := #[.submodules `CdclProof]
