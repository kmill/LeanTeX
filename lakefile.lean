import Lake
open Lake DSL

require "leanprover-community" / "proofwidgets" @ git "v0.0.53"

package LeanTeX { }

@[default_target]
lean_lib LeanTeX { }
