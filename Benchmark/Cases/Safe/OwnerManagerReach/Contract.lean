import Contracts.Common

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Verity model of the Safe OwnerManager linked list.
  The real contract maintains a circular singly-linked list of owner
  addresses using a mapping `owners : address => address` with a
  sentinel node at address 1.

  This benchmark models the four ownership-mutating functions from
  OwnerManager.sol and specifies reachability invariants from the
  Certora OwnerReach.spec.

  Upstream: safe-fndn/safe-smart-account (main)
  Commit: a2e19c6aa42a45ceec68057f3fa387f169c5b321
  File: contracts/base/OwnerManager.sol
-/

def SENTINEL : Address := 1

verity_contract OwnerManager where
  storage
    owners : Address → Uint256 := slot 0
    ownerCount : Uint256 := slot 1

  constants
    sentinel : Address := (wordToAddress 1)

  -- Models OwnerManager.setupOwners(_owners, _threshold).
  -- The real function loops over an array; this models the result of
  -- initializing a list with exactly three owners for specification
  -- purposes. The loop invariant (each inserted owner is fresh and
  -- valid) is encoded as require guards.
  -- Threshold setup is elided as it does not affect the owners mapping.
  function setupOwners (owner1 : Address, owner2 : Address, owner3 : Address) : Unit := do
    -- requireIsValidOwner for each owner
    require (owner1 != zeroAddress) "GS203"
    require (owner1 != sentinel) "GS203"
    require (owner2 != zeroAddress) "GS203"
    require (owner2 != sentinel) "GS203"
    require (owner3 != zeroAddress) "GS203"
    require (owner3 != sentinel) "GS203"
    -- No duplicates
    require (owner1 != owner2) "GS204"
    require (owner1 != owner3) "GS204"
    require (owner2 != owner3) "GS204"
    -- Build the linked list: SENTINEL → owner1 → owner2 → owner3 → SENTINEL
    setMappingAddr owners sentinel owner1
    setMappingAddr owners owner1 owner2
    setMappingAddr owners owner2 owner3
    setMappingAddr owners owner3 sentinel
    setStorage ownerCount 3

  -- Models OwnerManager.addOwnerWithThreshold(owner, _threshold).
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

  -- Models OwnerManager.removeOwner(prevOwner, owner, _threshold).
  -- Preconditions (requireCanRemoveOwner) are encoded as require guards.
  -- Threshold validation and update are elided.
  --
  -- Solidity:
  --   require(owners[prevOwner] == owner, "GS205");
  --   owners[prevOwner] = owners[owner];
  --   owners[owner] = address(0);
  --   ownerCount--;
  function removeOwner (prevOwner : Address, owner : Address) : Unit := do
    -- requireIsValidOwner
    require (owner != zeroAddress) "GS203"
    require (owner != sentinel) "GS203"
    -- requireCanRemoveOwner: owners[prevOwner] == owner
    let prevNext ← getMappingAddr owners prevOwner
    require (prevNext == owner) "GS205"
    -- Unlink: owners[prevOwner] = owners[owner]
    let ownerNext ← getMappingAddr owners owner
    setMappingAddr owners prevOwner ownerNext
    -- Clear: owners[owner] = address(0)
    setMappingAddr owners owner zeroAddress
    -- --ownerCount
    let count ← getStorage ownerCount
    setStorage ownerCount (sub count 1)

  -- Models OwnerManager.swapOwner(prevOwner, oldOwner, newOwner).
  -- Preconditions (requireCanAddOwner, requireCanRemoveOwner) are
  -- encoded as require guards. No threshold change.
  --
  -- Solidity:
  --   requireCanAddOwner(newOwner);
  --   requireCanRemoveOwner(prevOwner, oldOwner);
  --   owners[newOwner] = owners[oldOwner];
  --   owners[prevOwner] = newOwner;
  --   owners[oldOwner] = address(0);
  function swapOwner (prevOwner : Address, oldOwner : Address, newOwner : Address) : Unit := do
    -- requireIsValidOwner(newOwner)
    require (newOwner != zeroAddress) "GS203"
    require (newOwner != sentinel) "GS203"
    -- requireCanAddOwner(newOwner): owners[newOwner] == 0
    let newOwnerNext ← getMappingAddr owners newOwner
    require (newOwnerNext == zeroAddress) "GS204"
    -- requireCanRemoveOwner(prevOwner, oldOwner)
    require (oldOwner != zeroAddress) "GS203"
    require (oldOwner != sentinel) "GS203"
    let prevNext ← getMappingAddr owners prevOwner
    require (prevNext == oldOwner) "GS205"
    -- Swap: owners[newOwner] = owners[oldOwner]
    let oldOwnerNext ← getMappingAddr owners oldOwner
    setMappingAddr owners newOwner oldOwnerNext
    -- owners[prevOwner] = newOwner
    setMappingAddr owners prevOwner newOwner
    -- owners[oldOwner] = address(0)
    setMappingAddr owners oldOwner zeroAddress

end Benchmark.Cases.Safe.OwnerManagerReach
