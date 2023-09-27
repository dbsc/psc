import Lake
open Lake DSL

require base from git "https://github.com/AeneasVerif/aeneas.git"@"main"/"backends/lean"

package «test» {
  -- add package configuration options here
}

lean_lib «Test» {
  -- add library configuration options here
}

@[default_target]
lean_exe «test» {
  root := `Proofs
}
