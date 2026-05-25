/-
  Reference proof file for the `unlink_xyz/pool` case.

  `FormalAudit.lean` contains the named AP/IC proof obligations from the
  formal-audit definition report. This file keeps the original compile gate
  and imports the audit worklist so it is checked whenever the pool proof
  module is checked.
-/
import Benchmark.Cases.UnlinkXyz.Pool.Contract
import Benchmark.Cases.UnlinkXyz.Pool.FormalAudit

namespace Benchmark.Cases.UnlinkXyz.Pool

/-- The case is `build_green`, so the task target is the absence of
    elaboration errors in `Contract.lean`. -/
theorem unlinkPool_compiles : True := trivial

end Benchmark.Cases.UnlinkXyz.Pool
