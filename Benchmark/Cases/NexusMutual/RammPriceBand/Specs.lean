import Verity.Specs.Common
import Benchmark.Cases.NexusMutual.RammPriceBand.Contract

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

def syncPriceBand_sets_capital_spec
    (capital_ : Uint256) (_s s' : ContractState) : Prop :=
  s'.storage 0 = capital_

def syncPriceBand_sets_book_value_spec
    (capital_ supply_ : Uint256) (_s s' : ContractState) : Prop :=
  s'.storage 2 = div (mul 1000000000000000000 capital_) supply_

def syncPriceBand_sets_buy_price_spec
    (capital_ supply_ : Uint256) (_s s' : ContractState) : Prop :=
  let bv := div (mul 1000000000000000000 capital_) supply_
  s'.storage 3 = div (mul bv 10100) 10000

def syncPriceBand_sets_sell_price_spec
    (capital_ supply_ : Uint256) (_s s' : ContractState) : Prop :=
  let bv := div (mul 1000000000000000000 capital_) supply_
  s'.storage 4 = div (mul bv 9900) 10000

def syncPriceBand_sell_le_buy_spec
    (_s s' : ContractState) : Prop :=
  s'.storage 4 ≤ s'.storage 3

end Benchmark.Cases.NexusMutual.RammPriceBand

namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

/--
  The buy spot price is always at or above book value.
  Holds in both branches of calculateBuyReserve:
  - BV branch: nxmBuyReserve is at the target → buyPrice = bv * 1.01 ≥ bv
  - Ratchet branch: nxmBuyReserve is smaller than target → buyPrice is even higher
-/
def spotPrice_buy_ge_book_value_spec
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256) : Prop :=
  let (buyPrice, _sellPrice) := spotPrices eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
  let bookValue := div (mul ONE_ETHER capital) supply
  buyPrice ≥ bookValue

/--
  The sell spot price is always at or below book value.
  Holds in both branches of calculateSellReserve:
  - BV branch: nxmSellReserve is at the target → sellPrice = bv * 0.99 ≤ bv
  - Ratchet branch: nxmSellReserve is larger than target → sellPrice is even lower
-/
def spotPrice_sell_le_book_value_spec
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256) : Prop :=
  let (_buyPrice, sellPrice) := spotPrices eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
  let bookValue := div (mul ONE_ETHER capital) supply
  sellPrice ≤ bookValue

/--
  The sell spot price never exceeds the buy spot price.
  Together with the two specs above, this gives the full sandwich: sell ≤ bv ≤ buy.
-/
def spotPrice_sell_le_buy_spec
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256) : Prop :=
  let (buyPrice, sellPrice) := spotPrices eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
  sellPrice ≤ buyPrice

end Benchmark.Cases.NexusMutual.RammSpotPrice
