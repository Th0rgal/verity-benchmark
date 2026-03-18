import Verity.Specs.Common
import Benchmark.Cases.NexusMutual.RammPriceBand.Contract

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

def buy_price_above_book_value_buffer_spec (s' : ContractState) : Prop :=
  mul (s'.storage 3) 100 >= mul (s'.storage 2) 101

def sell_price_below_book_value_buffer_spec (s' : ContractState) : Prop :=
  mul (s'.storage 4) 100 <= mul (s'.storage 2) 99

def sell_price_below_buy_price_spec (s' : ContractState) : Prop :=
  s'.storage 4 <= s'.storage 3

end Benchmark.Cases.NexusMutual.RammPriceBand
