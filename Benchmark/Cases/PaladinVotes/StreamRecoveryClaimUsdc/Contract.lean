import Contracts.Common

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Minimal Verity slice of StreamRecoveryClaim._claimUsdc specialized to a single active
  round. Merkle verification is abstracted as a boolean input and token transfer side
  effects are omitted; the benchmark focuses on the accounting path that enforces
  "cannot claim more than allocated".
-/
verity_contract StreamRecoveryClaimUsdc where
  storage
    roundUsdcTotal : Uint256 := slot 0
    roundUsdcClaimed : Uint256 := slot 1
    totalUsdcAllocated : Uint256 := slot 2
    roundActive : Uint256 := slot 3
    hasSignedWaiver : Address → Uint256 := slot 4
    hasClaimedUsdc : Address → Uint256 := slot 5
    roundWethTotal : Uint256 := slot 6
    roundWethClaimed : Uint256 := slot 7
    totalWethAllocated : Uint256 := slot 8
    hasClaimedWeth : Address → Uint256 := slot 9

  function claimUsdc (shareWad : Uint256, proofAccepted : Bool) : Uint256 := do
    let sender ← msgSender
    let waiverSigned ← getMapping hasSignedWaiver sender
    let active ← getStorage roundActive
    let alreadyClaimed ← getMapping hasClaimedUsdc sender
    let roundTotal ← getStorage roundUsdcTotal
    let roundClaimed ← getStorage roundUsdcClaimed
    let totalAllocated ← getStorage totalUsdcAllocated

    require (waiverSigned != 0) "WaiverNotSigned"
    require (active != 0) "RoundNotActive"
    require (alreadyClaimed == 0) "AlreadyClaimed"
    require proofAccepted "InvalidProof"

    let amount := div (mul shareWad roundTotal) 1000000000000000000
    require (add roundClaimed amount <= roundTotal) "ClaimExceedsTotal"

    setMapping hasClaimedUsdc sender 1
    setStorage roundUsdcClaimed (add roundClaimed amount)
    setStorage totalUsdcAllocated (sub totalAllocated amount)
    return amount

  function claimableUsdc (shareWad : Uint256) : Uint256 := do
    let roundTotal ← getStorage roundUsdcTotal
    return (div (mul shareWad roundTotal) 1000000000000000000)

  function claimWeth (shareWad : Uint256, proofAccepted : Bool) : Uint256 := do
    let sender ← msgSender
    let waiverSigned ← getMapping hasSignedWaiver sender
    let active ← getStorage roundActive
    let alreadyClaimed ← getMapping hasClaimedWeth sender
    let roundTotal ← getStorage roundWethTotal
    let roundClaimed ← getStorage roundWethClaimed
    let totalAllocated ← getStorage totalWethAllocated

    require (waiverSigned != 0) "WaiverNotSigned"
    require (active != 0) "RoundNotActive"
    require (alreadyClaimed == 0) "AlreadyClaimed"
    require proofAccepted "InvalidProof"

    let amount := div (mul shareWad roundTotal) 1000000000000000000
    require (add roundClaimed amount <= roundTotal) "ClaimExceedsTotal"

    setMapping hasClaimedWeth sender 1
    setStorage roundWethClaimed (add roundClaimed amount)
    setStorage totalWethAllocated (sub totalAllocated amount)
    return amount

  function claimBoth
      (usdcShareWad : Uint256, usdcProofAccepted : Bool,
       wethShareWad : Uint256, wethProofAccepted : Bool) : Unit := do
    let sender ← msgSender

    let waiverSigned ← getMapping hasSignedWaiver sender
    let active ← getStorage roundActive
    let usdcAlreadyClaimed ← getMapping hasClaimedUsdc sender
    let usdcRoundTotal ← getStorage roundUsdcTotal
    let usdcRoundClaimed ← getStorage roundUsdcClaimed
    let usdcTotalAllocated ← getStorage totalUsdcAllocated

    require (waiverSigned != 0) "WaiverNotSigned"
    require (active != 0) "RoundNotActive"
    require (usdcAlreadyClaimed == 0) "AlreadyClaimed"
    require usdcProofAccepted "InvalidProof"

    let usdcAmount := div (mul usdcShareWad usdcRoundTotal) 1000000000000000000
    require (add usdcRoundClaimed usdcAmount <= usdcRoundTotal) "ClaimExceedsTotal"

    setMapping hasClaimedUsdc sender 1
    setStorage roundUsdcClaimed (add usdcRoundClaimed usdcAmount)
    setStorage totalUsdcAllocated (sub usdcTotalAllocated usdcAmount)

    let waiverSignedWeth ← getMapping hasSignedWaiver sender
    let activeWeth ← getStorage roundActive
    let wethAlreadyClaimed ← getMapping hasClaimedWeth sender
    let wethRoundTotal ← getStorage roundWethTotal
    let wethRoundClaimed ← getStorage roundWethClaimed
    let wethTotalAllocated ← getStorage totalWethAllocated

    require (waiverSignedWeth != 0) "WaiverNotSigned"
    require (activeWeth != 0) "RoundNotActive"
    require (wethAlreadyClaimed == 0) "AlreadyClaimed"
    require wethProofAccepted "InvalidProof"

    let wethAmount := div (mul wethShareWad wethRoundTotal) 1000000000000000000
    require (add wethRoundClaimed wethAmount <= wethRoundTotal) "ClaimExceedsTotal"

    setMapping hasClaimedWeth sender 1
    setStorage roundWethClaimed (add wethRoundClaimed wethAmount)
    setStorage totalWethAllocated (sub wethTotalAllocated wethAmount)
    return ()

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
