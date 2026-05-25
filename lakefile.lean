import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from "/workspaces/mission-fd475fe4/audit-workspace/verity-pin"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
