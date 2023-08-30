import Lake
open Lake DSL

package LeanTeX { }

@[default_target]
lean_lib LeanTeX { }

require std from git "https://github.com/leanprover/std4" @ "main"
