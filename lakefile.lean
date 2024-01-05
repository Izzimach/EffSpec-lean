import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.3.0"
require aesop from git "https://github.com/JLimperg/aesop"@"v4.3.0"

package effSpec {
  -- add any package configuration options here
  --moreServerArgs := #["-DautoImplicit=false"]
}

@[default_target]
lean_lib EffSpec {
  -- add any library configuration options here
  -- moreLeanArgs := #["-DautoImplicit=false"]
}
