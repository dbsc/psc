import Lake
open Lake DSL

package «psc» {
  -- add package configuration options here
}

lean_lib «Psc» {
  -- add library configuration options here
}

@[default_target]
lean_exe «psc» {
  root := `Main
}
