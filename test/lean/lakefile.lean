import Lake
open Lake DSL

require base from "/aeneas/backends/lean"

package «test» {
  -- add package configuration options here
}

lean_lib «Test» {
  -- add library configuration options here
}

@[default_target]
lean_exe «test» {
  root := `Main
}
