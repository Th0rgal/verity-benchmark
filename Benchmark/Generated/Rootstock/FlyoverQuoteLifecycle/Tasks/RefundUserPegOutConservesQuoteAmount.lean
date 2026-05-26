import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256

/-- User refund completes an expired quote and assigns the registered amount. -/
theorem refundUserPegOut_conserves_quote_amount
    (quoteHash : Address)
    (rskRefundAddress : Address)
    (transferSucceeds : Bool)
    (currentTimestamp currentBlock : Uint256)
    (s : ContractState)
    (hFallbackNoOverflow :
      add (s.storageMap 5 rskRefundAddress) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 rskRefundAddress)
    (_hUserRecipient : userRecipientMatchesStoredQuote quoteHash rskRefundAddress)
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    (hExpiredDate : (currentTimestamp > s.storageMap 9 quoteHash) = true)
    (hExpiredBlock : (currentBlock > s.storageMap 10 quoteHash) = true) :
    let s' := ((PegOutLifecycle.refundUserPegOut quoteHash rskRefundAddress transferSucceeds currentTimestamp currentBlock).run s).snd
    refundUserPegOut_conserves_quote_amount_spec quoteHash rskRefundAddress transferSucceeds currentTimestamp currentBlock s s' := by
  exact ?_

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
