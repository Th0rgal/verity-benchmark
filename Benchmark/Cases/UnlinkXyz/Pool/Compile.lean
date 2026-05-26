import Benchmark.Cases.UnlinkXyz.Pool.Specs
import Benchmark.Cases.UnlinkXyz.Pool.InternalLazyIMT
import Benchmark.Cases.UnlinkXyz.Pool.State
import Benchmark.Cases.UnlinkXyz.Pool.Contract
import Benchmark.Cases.UnlinkXyz.Pool.VerifierRouter
import Benchmark.Cases.UnlinkXyz.Pool.UnlinkPoolArtifact.UnlinkPoolArtifact
import Benchmark.Cases.UnlinkXyz.Pool.VerifierRouterArtifact.VerifierRouterArtifact
import Benchmark.Cases.UnlinkXyz.Pool.FormalAudit
import Benchmark.Cases.UnlinkXyz.Pool.Proofs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Compiler.CompilationModel
open Verity.EVM.Uint256

private def uintArray : ParamType :=
  ParamType.array ParamType.uint256

private def noteParam : ParamType :=
  ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.uint256]

private def ciphertextParam : ParamType :=
  ParamType.tuple [
    ParamType.uint256,
    ParamType.fixedArray ParamType.uint256 3
  ]

private def ciphertextArray : ParamType :=
  ParamType.array ciphertextParam

private def tokenPermissionsParam : ParamType :=
  ParamType.tuple [ParamType.address, ParamType.uint256]

private def permitTransferFromParam : ParamType :=
  ParamType.tuple [tokenPermissionsParam, ParamType.uint256, ParamType.uint256]

private def eventParamEq (a b : EventParam) : Bool :=
  a.name == b.name && a.ty == b.ty && a.kind == b.kind

private def eventDefEq (name : String) (params : List EventParam) (eventDef : EventDef) : Bool :=
  eventDef.name == name &&
    eventDef.params.length == params.length &&
    (eventDef.params.zip params).all (fun (actual, expected) => eventParamEq actual expected)

private def hasEvent (name : String) (params : List EventParam) : Bool :=
  UnlinkPool.spec.events.any (eventDefEq name params)

private def hasRouterEvent (name : String) (params : List EventParam) : Bool :=
  VerifierRouter.spec.events.any (eventDefEq name params)

private def hasRouterEntrypoint (name : String) : Bool :=
  VerifierRouter.spec.functions.any (fun fn => fn.name == name && !fn.isInternal)

private def hasPoolEntrypointWithRole (name role : String) : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == name && !fn.isInternal && fn.requiresRole == some role)

private def stmtIsInternalCall (callee : String) : Stmt → Bool
  | Stmt.internalCall name _ => name == callee || name == s!"internal_{callee}"
  | Stmt.internalCallAssign _ name _ => name == callee || name == s!"internal_{callee}"
  | _ => false

private def stmtListHasInternalCall (callee : String) (body : List Stmt) : Bool :=
  body.any (stmtIsInternalCall callee)

private def stmtHasRevertError (errorName : String) : Stmt → Bool
  | Stmt.revertError actual _ => actual == errorName
  | _ => false

private def stmtListHasRevertError (errorName : String) (body : List Stmt) : Bool :=
  body.any (stmtHasRevertError errorName)

private def stmtHasRequireError (errorName : String) : Stmt → Bool
  | Stmt.requireError _ actual _ => actual == errorName
  | _ => false

private def stmtListHasRequireError (errorName : String) (body : List Stmt) : Bool :=
  body.any (stmtHasRequireError errorName)

private def hasPoolEntrypointWithRequireError (name errorName : String) : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == name && !fn.isInternal && stmtListHasRequireError errorName fn.body)

private def hasPoolEntrypointWithoutRequireError (name errorName : String) : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == name && !fn.isInternal && !stmtListHasRequireError errorName fn.body)

private def stmtDirectWritesOnlyFields (allowed : List String) : Stmt → Bool
  | Stmt.setStorage field _ => allowed.contains field
  | Stmt.setStorageAddr field _ => allowed.contains field
  | Stmt.setStorageWord field _ _ => allowed.contains field
  | Stmt.storageArrayPush field _ => allowed.contains field
  | Stmt.storageArrayPop field => allowed.contains field
  | Stmt.setStorageArrayElement field _ _ => allowed.contains field
  | Stmt.setMapping field _ _ => allowed.contains field
  | Stmt.setMappingWord field _ _ _ => allowed.contains field
  | Stmt.setMappingPackedWord field _ _ _ _ => allowed.contains field
  | Stmt.setMapping2 field _ _ _ => allowed.contains field
  | Stmt.setMapping2Word field _ _ _ _ => allowed.contains field
  | Stmt.setMappingUint field _ _ => allowed.contains field
  | Stmt.setMappingChain field _ _ => allowed.contains field
  | Stmt.setStructMember field _ _ _ => allowed.contains field
  | Stmt.setStructMember2 field _ _ _ _ => allowed.contains field
  | Stmt.tstore _ _ => allowed.contains "REENTRANCY_GUARD_STORAGE"
  | _ => true

private def stmtWritesOnlyFields (allowed : List String) : Stmt → Bool
  | Stmt.ite _ thenBranch elseBranch =>
      thenBranch.all (stmtDirectWritesOnlyFields allowed) &&
        elseBranch.all (stmtDirectWritesOnlyFields allowed)
  | stmt => stmtDirectWritesOnlyFields allowed stmt

private def stmtListWritesOnlyFields (allowed : List String) (body : List Stmt) : Bool :=
  body.all (stmtWritesOnlyFields allowed)

private def stmtDirectWritesField (target : String) : Stmt → Bool
  | Stmt.setStorage field _ => field == target
  | Stmt.setStorageAddr field _ => field == target
  | Stmt.setStorageWord field _ _ => field == target
  | Stmt.storageArrayPush field _ => field == target
  | Stmt.storageArrayPop field => field == target
  | Stmt.setStorageArrayElement field _ _ => field == target
  | Stmt.setMapping field _ _ => field == target
  | Stmt.setMappingWord field _ _ _ => field == target
  | Stmt.setMappingPackedWord field _ _ _ _ => field == target
  | Stmt.setMapping2 field _ _ _ => field == target
  | Stmt.setMapping2Word field _ _ _ _ => field == target
  | Stmt.setMappingUint field _ _ => field == target
  | Stmt.setMappingChain field _ _ => field == target
  | Stmt.setStructMember field _ _ _ => field == target
  | Stmt.setStructMember2 field _ _ _ _ => field == target
  | _ => false

private def stmtWritesField (target : String) : Stmt → Bool
  | Stmt.ite _ thenBranch elseBranch =>
      thenBranch.any (stmtDirectWritesField target) ||
        elseBranch.any (stmtDirectWritesField target)
  | stmt => stmtDirectWritesField target stmt

private def stmtListWritesField (target : String) (body : List Stmt) : Bool :=
  body.any (stmtWritesField target)

def unlinkPoolEventMetadataMatchesSource : Bool :=
  hasEvent "Deposited" [
    { name := "depositor", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "notes", ty := ParamType.array noteParam, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "Transferred" [
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "Withdrawn" [
    { name := "to", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "note", ty := noteParam, kind := EventParamKind.unindexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "EmergencyWithdrawn" [
    { name := "to", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "note", ty := noteParam, kind := EventParamKind.unindexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "RelayerAdded" [
    { name := "relayer", ty := ParamType.address, kind := EventParamKind.indexed }
  ] &&
  hasEvent "RelayerRemoved" [
    { name := "relayer", ty := ParamType.address, kind := EventParamKind.indexed }
  ] &&
  hasEvent "VerifierRouterUpdated" [
    { name := "previousRouter", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "newRouter", ty := ParamType.address, kind := EventParamKind.indexed }
  ]

example : unlinkPoolEventMetadataMatchesSource = true := by native_decide

def unlinkPoolTransferWithBalanceCheckMatchesSource : Bool :=
  let helperOk :=
    UnlinkPool.spec.functions.any (fun fn =>
      fn.name == "transferWithBalanceCheck" &&
        fn.params.map (fun param => param.ty) == [
          permitTransferFromParam,
          ParamType.address,
          ParamType.bytes,
          ParamType.uint256,
          ParamType.bytes32
        ] &&
        fn.returns == [])
  let depositCallsHelper :=
    UnlinkPool.spec.functions.any (fun fn =>
      fn.name == "deposit" &&
        !fn.isInternal &&
        stmtListHasInternalCall "transferWithBalanceCheck" fn.body)
  helperOk && depositCallsHelper

example : unlinkPoolTransferWithBalanceCheckMatchesSource = true := by native_decide

def unlinkPoolTransferWithBalanceCheckEnforcesDelta : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == "transferWithBalanceCheck" &&
      stmtListHasRequireError "PoolDepositBalanceMismatch" fn.body)

example : unlinkPoolTransferWithBalanceCheckEnforcesDelta = true := by native_decide

private def hasPoolFieldSlot (name : String) (expectedSlot : Nat) : Bool :=
  UnlinkPool.spec.fields.any (fun field => field.name == name && field.slot == some expectedSlot)

private def hasPoolPackedFieldSlot (name : String) (expectedSlot offset width : Nat) : Bool :=
  UnlinkPool.spec.fields.any (fun field =>
    field.name == name &&
      field.slot == some expectedSlot &&
      field.packedBits == some { offset := offset, width := width })

def unlinkPoolStorageNamespacesMatchSource : Bool :=
  hasPoolFieldSlot "initializable_initialized"
    0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00 &&
  hasPoolFieldSlot "ownable_owner"
    0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300 &&
  hasPoolFieldSlot "ownable2Step_pendingOwner"
    0x237e158222e3e6968b72b9db0d8043aacf074ad9f650f0d1606b4d82ee432c00 &&
  hasPoolFieldSlot "state_merkleRoot"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000 &&
  hasPoolPackedFieldSlot "state_merkleTree_maxIndex"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb001 0 40 &&
  hasPoolPackedFieldSlot "state_merkleTree_numberOfLeaves"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb001 40 40 &&
  hasPoolFieldSlot "state_merkleTree_elements"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb002 &&
  hasPoolFieldSlot "state_rootSeen"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb003 &&
  hasPoolFieldSlot "state_nullifierHashes"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb004 &&
  hasPoolFieldSlot "state_verifierRouter"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb005 &&
  hasPoolFieldSlot "relayersSlot"
    0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00

example : unlinkPoolStorageNamespacesMatchSource = true := by native_decide

def unlinkPoolAdminEntrypointsHaveOwnerRole : Bool :=
  hasPoolEntrypointWithRole "authorizeUpgrade" "ownable_owner" &&
  hasPoolEntrypointWithRole "renounceOwnership" "ownable_owner" &&
  hasPoolEntrypointWithRole "addRelayer" "ownable_owner" &&
  hasPoolEntrypointWithRole "removeRelayer" "ownable_owner" &&
  hasPoolEntrypointWithRole "setVerifierRouter" "ownable_owner" &&
  hasPoolEntrypointWithRole "transferOwnership" "ownable_owner"

example : unlinkPoolAdminEntrypointsHaveOwnerRole = true := by native_decide

def unlinkPoolRenounceOwnershipDisabled : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == "renounceOwnership" &&
      !fn.isInternal &&
      fn.requiresRole == some "ownable_owner" &&
      stmtListHasRevertError "PoolRenounceOwnershipDisabled" fn.body)

example : unlinkPoolRenounceOwnershipDisabled = true := by native_decide

def unlinkPoolSetVerifierRouterOwnerGatedWriteSet : Bool :=
  UnlinkPool.spec.functions.any (fun fn =>
    fn.name == "setVerifierRouter" &&
      !fn.isInternal &&
      fn.requiresRole == some "ownable_owner" &&
      stmtListWritesField "state_verifierRouter" fn.body &&
      stmtListWritesOnlyFields ["state_verifierRouter"] fn.body)

example : unlinkPoolSetVerifierRouterOwnerGatedWriteSet = true := by native_decide

def unlinkPoolSnarkScalarFieldMatchesBn254Manifest : Bool :=
  PoolConstants.SNARK_SCALAR_FIELD =
    (0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001 : Verity.Uint256)

example : unlinkPoolSnarkScalarFieldMatchesBn254Manifest = true := by native_decide

def unlinkPoolRelayedEntrypointsRequireRelayer : Bool :=
  hasPoolEntrypointWithRequireError "deposit" "PoolUnauthorizedRelayer" &&
  hasPoolEntrypointWithRequireError "transfer" "PoolUnauthorizedRelayer" &&
  hasPoolEntrypointWithRequireError "withdraw" "PoolUnauthorizedRelayer"

example : unlinkPoolRelayedEntrypointsRequireRelayer = true := by native_decide

def unlinkPoolEmergencyWithdrawIsPermissionless : Bool :=
  hasPoolEntrypointWithoutRequireError "emergencyWithdraw" "PoolUnauthorizedRelayer"

example : unlinkPoolEmergencyWithdrawIsPermissionless = true := by native_decide

private def uint16Param : ParamType :=
  ParamType.uint16

def verifierRouterModelEventMetadataMatchesSource : Bool :=
  hasRouterEvent "CircuitRegistered" [
    { name := "circuitId", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "verifier", ty := ParamType.address, kind := EventParamKind.unindexed },
    { name := "inputCount", ty := uint16Param, kind := EventParamKind.unindexed },
    { name := "outputCount", ty := uint16Param, kind := EventParamKind.unindexed }
  ] &&
  hasRouterEvent "CircuitActiveSet" [
    { name := "circuitId", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "active", ty := ParamType.uint256, kind := EventParamKind.unindexed }
  ]

example : verifierRouterModelEventMetadataMatchesSource = true := by native_decide

def verifierRouterEntrypointsMatchSource : Bool :=
  hasRouterEntrypoint "setCircuit" &&
  hasRouterEntrypoint "pauseCircuit" &&
  hasRouterEntrypoint "getCircuit" &&
  hasRouterEntrypoint "verifierToCircuitId" &&
  hasRouterEntrypoint "renounceOwnership" &&
  hasRouterEntrypoint "owner" &&
  hasRouterEntrypoint "pendingOwner" &&
  hasRouterEntrypoint "transferOwnership" &&
  hasRouterEntrypoint "acceptOwnership"

example : verifierRouterEntrypointsMatchSource = true := by native_decide

private def functionParamTypes (fn : FunctionSpec) : List ParamType :=
  fn.params.map (fun param => param.ty)

private def hasRouterFunctionSignature
    (name : String) (params returns : List ParamType) : Bool :=
  VerifierRouter.spec.functions.any (fun fn =>
    fn.name == name &&
      functionParamTypes fn == params &&
      fn.returns == returns)

def verifierRouterFunctionMetadataMatchesSource : Bool :=
  hasRouterFunctionSignature "setCircuit"
    [ParamType.uint256, ParamType.address, uint16Param, uint16Param]
    [] &&
  hasRouterFunctionSignature "pauseCircuit"
    [ParamType.uint256]
    [] &&
  hasRouterFunctionSignature "getCircuit"
    [ParamType.uint256]
    [ParamType.address, uint16Param, uint16Param, ParamType.uint256] &&
  hasRouterFunctionSignature "verifierToCircuitId"
    [ParamType.address]
    [ParamType.uint256]

example : verifierRouterFunctionMetadataMatchesSource = true := by native_decide

private def hasStructMember
    (members : List StructMember) (name : String) (wordOffset offset width : Nat) : Bool :=
  members.any (fun member =>
    member.name == name &&
      member.wordOffset == wordOffset &&
      member.packed == some { offset := offset, width := width })

def verifierRouterCircuitStorageUsesMappingStruct : Bool :=
  VerifierRouter.spec.fields.any (fun field =>
    field.name == "circuits" &&
      match field.ty with
      | FieldType.mappingStruct MappingKeyType.uint256 members =>
          hasStructMember members "verifier" 0 0 160 &&
          hasStructMember members "inputCount" 0 160 16 &&
          hasStructMember members "outputCount" 0 176 16 &&
          hasStructMember members "active" 0 192 8
      | _ => false)

example : verifierRouterCircuitStorageUsesMappingStruct = true := by native_decide

def formalAuditConcreteAPICSurfacesGenerated : Bool :=
  unlinkPoolEventMetadataMatchesSource &&
  unlinkPoolTransferWithBalanceCheckMatchesSource &&
  unlinkPoolTransferWithBalanceCheckEnforcesDelta &&
  unlinkPoolStorageNamespacesMatchSource &&
  unlinkPoolAdminEntrypointsHaveOwnerRole &&
  unlinkPoolRenounceOwnershipDisabled &&
  unlinkPoolSetVerifierRouterOwnerGatedWriteSet &&
  unlinkPoolSnarkScalarFieldMatchesBn254Manifest &&
  unlinkPoolRelayedEntrypointsRequireRelayer &&
  unlinkPoolEmergencyWithdrawIsPermissionless &&
  verifierRouterModelEventMetadataMatchesSource &&
  verifierRouterFunctionMetadataMatchesSource &&
  verifierRouterCircuitStorageUsesMappingStruct

example : formalAuditConcreteAPICSurfacesGenerated = true := by native_decide

def generatedArtifactsResolveToGeneratedSpecs : Prop :=
  UnlinkPoolArtifact.spec = UnlinkPool.spec ∧
  VerifierRouterArtifact.spec = VerifierRouter.spec

theorem generatedArtifactsResolveToGeneratedSpecs_true :
    generatedArtifactsResolveToGeneratedSpecs := by
  simp [generatedArtifactsResolveToGeneratedSpecs,
    UnlinkPoolArtifact.spec, VerifierRouterArtifact.spec]

def formalAuditReadyFromGeneratedArtifacts : Prop :=
  FormalAudit.formalAuditReadyForDelivery ∧
  formalAuditConcreteAPICSurfacesGenerated = true ∧
  generatedArtifactsResolveToGeneratedSpecs

theorem formalAuditReadyFromGeneratedArtifacts_true :
    formalAuditReadyFromGeneratedArtifacts := by
  exact ⟨FormalAudit.formal_audit_ready_for_delivery,
    by native_decide,
    generatedArtifactsResolveToGeneratedSpecs_true⟩

def caseReady : Bool := true

end Benchmark.Cases.UnlinkXyz.Pool
