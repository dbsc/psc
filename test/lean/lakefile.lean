import Lake
open Lake DSL

require base from "/aeneas/backends/lean"

package «psc» {
  -- add package configuration options here
}

lean_lib «Psc» {
  -- add library configuration options here
}

lean_lib «Base» {
  srcDir := "/aeneas/backends/lean"
}

@[default_target]
lean_exe «psc» {
  root := `Main
}
