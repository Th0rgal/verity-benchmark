import Benchmark.Cases.NexusMutual.RammPriceBand.Specs

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

/--
The synchronized buy quote stays at or above the buffered book-value floor.
-/
theorem buy_price_ge_book_value_buffer
    (s' : ContractState) :
    buy_price_above_book_value_buffer_spec s' ->
    mul (s'.storage 3) 100 >= mul (s'.storage 2) 101 := by
  intro hBuyBound
  simpa [buy_price_above_book_value_buffer_spec] using hBuyBound

/--
The synchronized sell quote stays at or below the buffered book-value ceiling.
-/
theorem sell_price_le_book_value_buffer
    (s' : ContractState) :
    sell_price_below_book_value_buffer_spec s' ->
    mul (s'.storage 4) 100 <= mul (s'.storage 2) 99 := by
  intro hSellBound
  simpa [sell_price_below_book_value_buffer_spec] using hSellBound

/--
The synchronized sell quote never exceeds the buy quote.
-/
theorem sell_price_le_buy_price
    (s' : ContractState) :
    sell_price_below_buy_price_spec s' ->
    s'.storage 4 <= s'.storage 3 := by
  intro hOrdering
  simpa [sell_price_below_buy_price_spec] using hOrdering

end Benchmark.Cases.NexusMutual.RammPriceBand
