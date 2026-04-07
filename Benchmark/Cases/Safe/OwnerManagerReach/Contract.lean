import Contracts.Common

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity slice of the Safe OwnerManager linked list.
  The real contract maintains a circular singly-linked list of owner
  addresses using a mapping `owners : address => address` with a
  sentinel node at address 1.

  This benchmark models `addOwnerWithThreshold` and proves the
  `inListReachable` invariant from the Certora OwnerReach.spec:
  every node with a non-zero successor is reachable from SENTINEL.

  Upstream: safe-fndn/safe-smart-account (main)
  File: contracts/base/OwnerManager.sol
-/

def SENTINEL : Address := 1

verity_contract OwnerManager where
  storage
    owners : Address → Uint256 := slot 0
    ownerCount : Uint256 := slot 1

  constants
    sentinel : Address := (wordToAddress 1)

  -- Models OwnerManager.addOwnerWithThreshold (owner, _threshold).
  -- Preconditions (requireCanAddOwner) are encoded as require guards.
  -- Threshold update is elided as it does not affect the owners mapping.
  function addOwner (owner : Address) : Unit := do
    -- requireIsValidOwner: owner != 0 && owner != SENTINEL
    require (owner != zeroAddress) "GS203"
    require (owner != sentinel) "GS203"
    -- requireCanAddOwner: owners[owner] == 0 (no duplicates)
    let ownerNext ← getMappingAddr owners owner
    require (ownerNext == zeroAddress) "GS204"
    -- Insert at head: owners[owner] = owners[SENTINEL]; owners[SENTINEL] = owner
    let head ← getMappingAddr owners sentinel
    setMappingAddr owners owner head
    setMappingAddr owners sentinel owner
    -- ++ownerCount
    let count ← getStorage ownerCount
    setStorage ownerCount (add count 1)

end Benchmark.Cases.Safe.OwnerManagerReach
