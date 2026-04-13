import Contracts.Common

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Focused Verity slice of Nexus Mutual's RAMM pricing surface.
  The real contract derives buy and sell prices from reserves, ratchets, and a
  1% buffer around book value. This benchmark freezes that invariant-relevant
  boundary computation and omits reserve adjustment, TWAP, and swap execution.

  Trust assumptions:
  - `capital_` is taken as a trusted input. In the real contract it comes from
    `pool.getPoolValueInEth()`, which aggregates multi-asset balances via
    Chainlink oracle feeds. Oracle correctness, staleness, and manipulation
    resistance are outside the scope of this proof.
  - `supply_` is taken as a trusted input. In the real contract it comes from
    `tokenController.totalSupply()`.
-/
verity_contract RammPriceBand where
  storage
    capital : Uint256 := slot 0
    supply : Uint256 := slot 1
    bookValue : Uint256 := slot 2
    buySpotPrice : Uint256 := slot 3
    sellSpotPrice : Uint256 := slot 4

  function syncPriceBand (capital_ : Uint256, supply_ : Uint256) : Unit := do
    require (supply_ != 0) "SupplyMustBePositive"

    let bv := div (mul 1000000000000000000 capital_) supply_
    let buy := div (mul bv 10100) 10000
    let sell := div (mul bv 9900) 10000

    setStorage capital capital_
    setStorage supply supply_
    setStorage bookValue bv
    setStorage buySpotPrice buy
    setStorage sellSpotPrice sell

end Benchmark.Cases.NexusMutual.RammPriceBand

/-
  Extended Verity model of Nexus Mutual's RAMM pricing with the ratchet mechanism.

  The RAMM has two AMM curves sharing one ETH reserve:
  - Buy curve:  uses `nxmBuyReserve`.  buyPrice  = 1e18 * eth / nxmBuyReserve
  - Sell curve: uses `nxmSellReserve`. sellPrice = 1e18 * eth / nxmSellReserve

  Smaller nxmBuyReserve  → higher buy price  (farther above book value).
  Larger  nxmSellReserve → lower  sell price (farther below book value).

  `calculateNxm` recomputes each reserve with two branches:
    1. BV branch    — ratchet has converged; snap reserve to book value ± 1%
    2. Ratchet branch — still converging; gradually move reserve toward target

  Trust assumptions:
  - `capital` and `supply` are trusted inputs (oracle + token supply).
  - `oldEth`, `oldNxmBuyReserve`, `oldNxmSellReserve` are the previous reserve
    state; taken as free parameters (covers any post-swap or post-adjustEth state).
  - `elapsed` is block.timestamp − state.timestamp.
  - `speed` is the ratchet speed (400 normal, 5000 fast); proof holds for any value.
-/
namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

/-- Constants matching the Solidity contract -/
def PRICE_BUFFER : Uint256 := 100
def PRICE_BUFFER_DENOMINATOR : Uint256 := 10000
def RATCHET_PERIOD : Uint256 := 86400        -- 1 day in seconds
def RATCHET_DENOMINATOR : Uint256 := 10000
def ONE_ETHER : Uint256 := 1000000000000000000

/--
  Pure model of Solidity `calculateNxm` for the buy side (isAbove = true).

  Computes the NXM buy reserve. A smaller reserve means a higher buy price.

  Two branches:
  - BV branch: ratchet converged → reserve = eth * supply / (capital * 1.01)
  - Ratchet branch: still converging → reserve = eth * scaledReserve / (eth - ratchetTerm)
-/
def calculateBuyReserve
    (eth oldEth oldNxmBuyReserve capital supply elapsed speed : Uint256) : Uint256 :=
  -- Step 1: scale old reserve to current ETH level
  let scaledReserve := div (mul oldNxmBuyReserve eth) oldEth
  -- Step 2: compute BV + 1% target
  let bufferedCapital := div (mul capital (add PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR
  -- Step 3: ratchet term for the denominator (Solidity division order: / supply / period / denom)
  -- Solidity: capital * nxm * elapsed * NORMAL_RATCHET_SPEED / context.supply / RATCHET_PERIOD / RATCHET_DENOMINATOR
  let ratchetTerm := div (div (div (mul (mul (mul capital scaledReserve) elapsed) speed) supply) RATCHET_PERIOD) RATCHET_DENOMINATOR
  -- Step 4: convergence check (Solidity division order: / period / denom)
  -- Solidity: bufferedCapital * nxm + bufferedCapital * nxm * elapsed * speed / RATCHET_PERIOD / RATCHET_DENOMINATOR > eth * supply
  let base := mul bufferedCapital scaledReserve
  let ratchetExtra := div (div (mul (mul base elapsed) speed) RATCHET_PERIOD) RATCHET_DENOMINATOR
  if add base ratchetExtra > mul eth supply
  then div (mul eth supply) bufferedCapital                    -- BV branch
  else div (mul eth scaledReserve) (sub eth ratchetTerm)       -- ratchet branch

/--
  Pure model of Solidity `calculateNxm` for the sell side (isAbove = false).

  Computes the NXM sell reserve. A larger reserve means a lower sell price.

  Two branches:
  - BV branch: ratchet converged → reserve = eth * supply / (capital * 0.99)
  - Ratchet branch: still converging → reserve = eth * scaledReserve / (eth + ratchetTerm)
-/
def calculateSellReserve
    (eth oldEth oldNxmSellReserve capital supply elapsed speed : Uint256) : Uint256 :=
  -- Step 1: scale old reserve to current ETH level
  let scaledReserve := div (mul oldNxmSellReserve eth) oldEth
  -- Step 2: compute BV - 1% target
  let bufferedCapital := div (mul capital (sub PRICE_BUFFER_DENOMINATOR PRICE_BUFFER)) PRICE_BUFFER_DENOMINATOR
  -- Step 3: ratchet term for the denominator (Solidity division order: / supply / period / denom)
  -- Solidity: capital * nxm * elapsed * ratchetSpeedB / context.supply / RATCHET_PERIOD / RATCHET_DENOMINATOR
  let ratchetTerm := div (div (div (mul (mul (mul capital scaledReserve) elapsed) speed) supply) RATCHET_PERIOD) RATCHET_DENOMINATOR
  -- Step 4: convergence check (Solidity division order: / period / denom — no / supply)
  -- Solidity: bufferedCapital * nxm < eth * supply + capital * nxm * elapsed * ratchetSpeedB / RATCHET_PERIOD / RATCHET_DENOMINATOR
  let base := mul bufferedCapital scaledReserve
  let ratchetExtra := div (div (mul (mul (mul capital scaledReserve) elapsed) speed) RATCHET_PERIOD) RATCHET_DENOMINATOR
  if base < add (mul eth supply) ratchetExtra
  then div (mul eth supply) bufferedCapital                    -- BV branch
  else div (mul eth scaledReserve) (add eth ratchetTerm)       -- ratchet branch

/--
  Computes the spot prices from the NXM reserves:
    buyPrice  = 1e18 * eth / nxmBuyReserve
    sellPrice = 1e18 * eth / nxmSellReserve
-/
def spotPrices
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256) :
    Uint256 × Uint256 :=
  let nxmBuyReserve  := calculateBuyReserve  eth oldEth oldNxmBuyReserve  capital supply elapsed speed
  let nxmSellReserve := calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed
  let buyPrice  := div (mul ONE_ETHER eth) nxmBuyReserve
  let sellPrice := div (mul ONE_ETHER eth) nxmSellReserve
  (buyPrice, sellPrice)

end Benchmark.Cases.NexusMutual.RammSpotPrice
