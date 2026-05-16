/-
  Verity model of `VerifierRouter`.

  Upstream: unlink-xyz/monorepo@4bc46c1fffbc0e146dccfff5b9fe00167121b27b
  Source:   protocol/contracts/src/VerifierRouter.sol

  The source storage shape is preserved with a struct-valued mapping:

    mapping(bytes32 => Circuit) private _circuits;

  represented as `MappingStruct(Uint256, ...)`, with `bytes32` circuit ids
  carried as `Uint256` words. The Solidity `Circuit` return is emitted as the
  ABI-equivalent `Tuple [Address, Uint256, Uint256, Uint256]` because current
  `verity_contract` rejects named struct return types; the storage layout and
  member access remain struct-based.
-/
import Contracts.Common

namespace Benchmark.Cases.UnlinkXyz.Pool

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract VerifierRouter where
  storage
    ownerSlot        : Address := slot 0
    pendingOwnerSlot : Address := slot 1
    circuits : MappingStruct(Uint256,[
      verifier @word 0 packed(0,160),
      inputCount @word 0 packed(160,16),
      outputCount @word 0 packed(176,16),
      active @word 0 packed(192,8)
    ]) := slot 2
    verifierToCircuitIdSlot : Address → Uint256 := slot 3

  struct Circuit where
    verifier : Address,
    inputCount : Uint256,
    outputCount : Uint256,
    active : Uint256

  errors
    error VerifierRouterInvalidCircuitId ()
    error VerifierRouterInvalidVerifier ()
    error VerifierRouterInvalidShape ()
    error VerifierRouterShapeImmutable ()
    error VerifierRouterDuplicateVerifier ()
    error VerifierRouterUnknownCircuit (Uint256)
    error VerifierRouterRenounceOwnershipDisabled ()
    error CallerNotPendingOwner ()

  event_defs
    event CircuitRegistered(@indexed circuitId : Uint256, verifier : Address,
      inputCount : Uint256, outputCount : Uint256)
    event CircuitActiveSet(@indexed circuitId : Uint256, active : Uint256)
    event OwnershipTransferStarted(@indexed previousOwner : Address, @indexed newOwner : Address)
    event OwnershipTransferred(@indexed previousOwner : Address, @indexed newOwner : Address)

  constants
    FALSE_WORD : Uint256 := 0
    TRUE_WORD  : Uint256 := 1

  constructor () := do
    let sender ← msgSender
    setStorageAddr ownerSlot sender

  function view owner () : Address := do
    let current ← getStorageAddr ownerSlot
    return current

  function view pendingOwner () : Address := do
    let pending ← getStorageAddr pendingOwnerSlot
    return pending

  function transferOwnership (newOwner : Address)
      requires(ownerSlot) : Unit := do
    setStorageAddr pendingOwnerSlot newOwner
    let currentOwner ← getStorageAddr ownerSlot
    emit "OwnershipTransferStarted" [addressToWord currentOwner, addressToWord newOwner]

  function acceptOwnership () : Unit := do
    let sender ← msgSender
    let pending ← getStorageAddr pendingOwnerSlot
    requireError (sender == pending) CallerNotPendingOwner()
    let previousOwner ← getStorageAddr ownerSlot
    setStorageAddr ownerSlot pending
    setStorageAddr pendingOwnerSlot zeroAddress
    emit "OwnershipTransferred" [addressToWord previousOwner, addressToWord pending]

  function setCircuit
      (circuitId : Uint256, verifierAddr : Address, inputCount : Uint256,
       outputCount : Uint256)
      requires(ownerSlot) : Unit := do
    requireError (circuitId != 0) VerifierRouterInvalidCircuitId()
    requireError (verifierAddr != zeroAddress) VerifierRouterInvalidVerifier()
    let codeLen := extcodesize (addressToWord verifierAddr)
    requireError (codeLen != 0) VerifierRouterInvalidVerifier()
    requireError (inputCount != 0) VerifierRouterInvalidShape()
    requireError (outputCount != 0) VerifierRouterInvalidShape()

    let oldVerifier ← structMember "circuits" circuitId "verifier"
    let oldActive ← structMember "circuits" circuitId "active"
    if oldVerifier != zeroAddress then
      let oldInputCount ← structMember "circuits" circuitId "inputCount"
      let oldOutputCount ← structMember "circuits" circuitId "outputCount"
      requireError (oldInputCount == inputCount) VerifierRouterShapeImmutable()
      requireError (oldOutputCount == outputCount) VerifierRouterShapeImmutable()
    else
      pure ()

    let existingIdForVerifier ← getMapping verifierToCircuitIdSlot verifierAddr
    if existingIdForVerifier != FALSE_WORD then
      requireError (existingIdForVerifier == circuitId) VerifierRouterDuplicateVerifier()
    else
      pure ()

    if oldVerifier != zeroAddress then
      if oldVerifier != verifierAddr then
        setMapping verifierToCircuitIdSlot oldVerifier FALSE_WORD
      else
        pure ()
    else
      pure ()

    setMapping verifierToCircuitIdSlot verifierAddr circuitId
    setStructMember "circuits" circuitId "verifier" verifierAddr
    setStructMember "circuits" circuitId "inputCount" inputCount
    setStructMember "circuits" circuitId "outputCount" outputCount
    setStructMember "circuits" circuitId "active" TRUE_WORD
    emit "CircuitRegistered"
      [circuitId, addressToWord verifierAddr, inputCount, outputCount]
    if oldVerifier != zeroAddress then
      if oldActive == FALSE_WORD then
        emit "CircuitActiveSet" [circuitId, TRUE_WORD]
      else
        pure ()
    else
      pure ()

  function pauseCircuit (circuitId : Uint256)
      requires(ownerSlot) : Unit := do
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    requireError (verifierAddr != zeroAddress) VerifierRouterUnknownCircuit(circuitId)
    setStructMember "circuits" circuitId "active" FALSE_WORD
    emit "CircuitActiveSet" [circuitId, FALSE_WORD]

  function view getCircuit
      (circuitId : Uint256) : Tuple [Address, Uint256, Uint256, Uint256] := do
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    let inputCount ← structMember "circuits" circuitId "inputCount"
    let outputCount ← structMember "circuits" circuitId "outputCount"
    let active ← structMember "circuits" circuitId "active"
    return (verifierAddr, inputCount, outputCount, active)

  function view verifierToCircuitId (verifierAddr : Address) : Uint256 := do
    let circuitId ← getMapping verifierToCircuitIdSlot verifierAddr
    return circuitId

  function renounceOwnership ()
      requires(ownerSlot) : Unit := do
    revert VerifierRouterRenounceOwnershipDisabled()

end Benchmark.Cases.UnlinkXyz.Pool
