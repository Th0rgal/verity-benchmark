import Benchmark.Cases.UnlinkXyz.Pool.Compile

namespace Benchmark.Cases.UnlinkXyz.Pool
namespace FormalAudit

/--
Task-facing delivery gate for the UnlinkPool AP/IC audit.
-/
def formalAuditReady :=
  formalAuditReadyForDelivery

theorem formalAuditReady_compile_gate :
    Benchmark.Cases.UnlinkXyz.Pool.caseReady = true ∧
    formalAuditReady ∧
    Benchmark.Cases.UnlinkXyz.Pool.formalAuditReadyFromGeneratedArtifacts := by
  exact ⟨rfl,
    Benchmark.Cases.UnlinkXyz.Pool.FormalAudit.formal_audit_ready_for_delivery,
    Benchmark.Cases.UnlinkXyz.Pool.formalAuditReadyFromGeneratedArtifacts_true⟩

end FormalAudit
end Benchmark.Cases.UnlinkXyz.Pool
