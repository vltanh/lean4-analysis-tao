import Lake
open Lake DSL

package «lean4-analysis-tao» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "v4.16.0"

@[default_target]
lean_lib «Lean4AnalysisTao» where
  -- add any library configuration options here
