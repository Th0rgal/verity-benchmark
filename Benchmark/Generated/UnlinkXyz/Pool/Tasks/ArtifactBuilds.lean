import Benchmark.Cases.UnlinkXyz.Pool.Compile

namespace Benchmark.Cases.UnlinkXyz.Pool

/--
Build-green artifact-integrity task for the generated UnlinkPool bytecode path.
This imports the generated pool/router artifacts through `Compile` and checks
the concrete AP/IC surface flags computed from the generated declarations.
-/
theorem artifactBuilds_compile_gate :
    caseReady = true ∧
    formalAuditConcreteAPICSurfacesGenerated = true ∧
    generatedArtifactsResolveToGeneratedSpecs := by
  exact ⟨rfl, by native_decide, generatedArtifactsResolveToGeneratedSpecs_true⟩

end Benchmark.Cases.UnlinkXyz.Pool
