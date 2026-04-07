import Contracts.Common

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Focused Verity slice of the Lido VaultHub _locked() function.
  The real contract computes how much collateral must be locked on a vault to
  cover its stETH liability plus a reserve ratio buffer.

  This benchmark isolates the pure arithmetic of `_locked` and models
  `getPooledEthBySharesRoundUp` as an axiomatised share-to-ether conversion.
  Oracle, rebalance, and minting machinery are elided.

  Upstream: lidofinance/core (master)
  File: contracts/0.8.25/vaults/VaultHub.sol
-/

/-- Total basis points constant (10000) -/
def TOTAL_BASIS_POINTS : Uint256 := 10000

/--
  Overflow-safe ceiling division, matching Solidity's Math256.ceilDiv / OpenZeppelin:
    a == 0 ? 0 : (a - 1) / b + 1
  Uses EVM-level sub/div/add rather than Nat-level arithmetic.
-/
def ceilDiv (a b : Uint256) : Uint256 :=
  if a = 0 then 0
  else add (div (sub a 1) b) 1

/--
  Share-to-ether conversion matching Lido's getPooledEthBySharesRoundUp:
    Math256.ceilDiv(shares * totalPooledEther, totalShares)
  We treat totalPooledEther and totalShares as parameters.
-/
def getPooledEthBySharesRoundUp
    (shares : Uint256) (totalPooledEther totalShares : Uint256) : Uint256 :=
  ceilDiv (mul shares totalPooledEther) totalShares

verity_contract VaultHubLocked where
  storage
    -- VaultRecord fields
    maxLiabilityShares : Uint256 := slot 0
    liabilityShares : Uint256 := slot 1
    minimalReserve : Uint256 := slot 2
    -- VaultConnection field
    reserveRatioBP : Uint256 := slot 3
    -- Lido protocol state (axiomatised external reads)
    totalPooledEther : Uint256 := slot 4
    totalShares : Uint256 := slot 5
    -- Output: computed locked amount
    lockedAmount : Uint256 := slot 6

  -- Executable entrypoint modelling VaultHub._locked().
  -- Reads vault/Lido state from storage, computes the locked collateral amount
  -- using maxLiabilityShares (the peak shares in the current oracle period),
  -- stores the result, and returns it.
  --
  -- The ceilDiv logic is inlined because verity_contract does not yet support
  -- calling external helpers inside the function body (see #1003).
  --
  -- Solidity source (VaultHub.sol):
  --   uint256 liability = _getPooledEthBySharesRoundUp(_liabilityShares);
  --   uint256 reserve = Math256.ceilDiv(liability * _reserveRatioBP,
  --                                      TOTAL_BASIS_POINTS - _reserveRatioBP);
  --   return liability + Math256.max(reserve, _minimalReserve);
  function syncLocked () : Uint256 := do
    let maxLiabilityShares_ ← getStorage maxLiabilityShares
    let minimalReserve_ ← getStorage minimalReserve
    let reserveRatioBP_ ← getStorage reserveRatioBP
    let totalPooledEther_ ← getStorage totalPooledEther
    let totalShares_ ← getStorage totalShares

    -- getPooledEthBySharesRoundUp(maxLiabilityShares, totalPooledEther, totalShares)
    let liabilityProduct := mul maxLiabilityShares_ totalPooledEther_
    let liability := ite (liabilityProduct == 0) 0 (add (div (sub liabilityProduct 1) totalShares_) 1)
    -- ceilDiv(liability * reserveRatioBP, TOTAL_BASIS_POINTS - reserveRatioBP)
    let reserveInput := mul liability reserveRatioBP_
    let reserveDenominator := sub 10000 reserveRatioBP_
    let reserve := ite (reserveInput == 0) 0 (add (div (sub reserveInput 1) reserveDenominator) 1)
    -- Math256.max(reserve, minimalReserve)
    let effectiveReserve := ite (reserve >= minimalReserve_) reserve minimalReserve_
    let amount := add liability effectiveReserve

    setStorage lockedAmount amount
    return amount

end Benchmark.Cases.Lido.VaulthubLocked
