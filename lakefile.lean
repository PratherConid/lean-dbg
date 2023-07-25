import Lake
open Lake DSL

package «lean-dbg» {
  -- add package configuration options here
}

lean_lib LeanDbg {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean-dbg» {
  root := `Main
}
