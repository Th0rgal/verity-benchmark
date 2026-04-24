import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"57d47acd44f273df9848bc2df612d2daa8aedf18"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
