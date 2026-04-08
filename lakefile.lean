import Lake
open Lake DSL

package daboussi_pnt where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from "mathlib4-4.29.0"
lean_lib «Daboussi_pnt» where
  srcDir := "."
@[default_target]
lean_exe «daboussi_pnt» where
  root := `Main
