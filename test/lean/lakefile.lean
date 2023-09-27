import Lake
open Lake DSL

require base from git "https://github.com/AeneasVerif/aeneas.git"@"main"/"backends/lean"

package «psc» {
  -- add package configuration options here
}

lean_lib «Psc» {
  -- add library configuration options here
}

@[default_target]
lean_exe «psc» {
  root := `Proofs
}
