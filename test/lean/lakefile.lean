import Lake
open Lake DSL

require base from "../../../../aeneas/backends/lean"

package «psc» {
  -- add package configuration options here
}

lean_lib «Psc» {
  -- add library configuration options here
}

@[default_target]
lean_exe «test» {
  root := `Main
}
