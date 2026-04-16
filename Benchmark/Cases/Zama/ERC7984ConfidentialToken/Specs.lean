import Verity.Specs.Common
import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Contract

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/-
  Specifications for the ERC-7984 Confidential Token.

  These properties verify the core accounting logic of the confidential
  token, which is the primary target for formal verification. The FHE
  layer provides confidentiality; this layer provides correctness.

  Storage layout (from verity_contract ERC7984):
    slot 0: totalSupply
    slot 1 (mapping): balances
    slot 2 (mapping): balanceInitialized
-/

/-! ## Helpers -/

-- Read balance from state (mapping at slot 1)
def balanceOf (s : ContractState) (addr : Address) : Uint256 :=
  s.storageMap 1 addr

-- Read total supply from state (slot 0)
def supply (s : ContractState) : Uint256 :=
  s.storage 0

/-! ## Transfer specifications

  The transfer function models _update(from, to, amount) for from != 0, to != 0.
  The key semantic difference from ERC-20: insufficient balance causes a silent
  0-transfer instead of a revert.
-/

/--
  Transfer conservation: the sum of sender and receiver balances is preserved.
  This holds regardless of whether the transfer succeeds or silently transfers 0.
  balances[from] + balances[to] is the same before and after.

  This is the fundamental accounting invariant for any token.
-/
def transfer_conservation_spec
    (sender recipient : Address) (s s' : ContractState) : Prop :=
  add (balanceOf s' sender) (balanceOf s' recipient) =
  add (balanceOf s sender) (balanceOf s recipient)

/--
  Sufficient balance: when the sender has enough tokens, the transfer
  moves exactly `amount` from sender to receiver.
-/
def transfer_sufficient_spec
    (sender recipient : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  balanceOf s sender >= amount →
  balanceOf s' sender = sub (balanceOf s sender) amount ∧
  balanceOf s' recipient = add64 (balanceOf s recipient) amount

/--
  Insufficient balance: when the sender does not have enough tokens,
  no tokens move. Both balances are unchanged.
  This is the defining semantic of ERC-7984 vs ERC-20.
-/
def transfer_insufficient_spec
    (sender recipient : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  ¬(balanceOf s sender >= amount) →
  balanceOf s' sender = balanceOf s sender ∧
  balanceOf s' recipient = balanceOf s recipient

/--
  Transfer does not affect total supply. Only mint and burn change supply.
-/
def transfer_preserves_supply_spec
    (s s' : ContractState) : Prop :=
  supply s' = supply s

/-! ## Mint specifications -/

/--
  Successful mint: when totalSupply + amount does not overflow uint64,
  totalSupply increases by amount and receiver balance increases by amount.
-/
def mint_increases_supply_spec
    (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  (tryIncrease64 (supply s) amount).1 = true →
  supply s' = add64 (supply s) amount ∧
  balanceOf s' to = add64 (balanceOf s to) amount

/--
  Mint overflow protection: when totalSupply + amount would overflow uint64,
  no tokens are minted. totalSupply is unchanged. Receiver balance is unchanged.
-/
def mint_overflow_protection_spec
    (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  (tryIncrease64 (supply s) amount).1 = false →
  supply s' = supply s ∧
  balanceOf s' to = add64 (balanceOf s to) 0

/-! ## Burn specifications -/

/--
  Successful burn: when the sender has sufficient balance, fromBalance
  decreases by amount and totalSupply decreases by amount.
-/
def burn_decreases_supply_spec
    (holder : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  balanceOf s holder >= amount →
  balanceOf s' holder = sub (balanceOf s holder) amount ∧
  supply s' = sub64 (supply s) amount

/--
  Insufficient burn: when the sender does not have enough tokens,
  no tokens are burned. Both balance and totalSupply are unchanged.
-/
def burn_insufficient_spec
    (holder : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  ¬(balanceOf s holder >= amount) →
  balanceOf s' holder = balanceOf s holder ∧
  supply s' = supply s

/-! ## Non-leakage specification -/

/--
  Transfer never reverts based on balance sufficiency.

  Given that all plaintext preconditions hold (non-zero addresses,
  initialized balance), the transfer function always succeeds —
  it never reverts due to the encrypted balance comparison.

  This is the contract-level non-leakage invariant: an on-chain observer
  cannot distinguish a sufficient transfer from an insufficient one by
  observing whether the transaction reverted. The balance comparison
  only affects the encrypted VALUES written (via FHE.select), never
  the control flow (success vs revert).

  In the real contract, both paths execute identical EVM operations:
    tryDecrease → write balances[from] → select → write balances[to]
  No require/revert depends on the encrypted comparison result.
-/
def transfer_no_balance_revert_spec
    (sender recipient : Address) (amount : Uint256) (s : ContractState) : Prop :=
  ((ERC7984.transfer sender recipient amount).run s).isSuccess = true

/-! ## Operator specification -/

/--
  Operator authorization: transferFrom with a valid operator (either the
  holder themselves, or an operator whose expiry >= block.timestamp)
  behaves identically to a direct transfer. The returned transferred
  amount is the same.
-/
def transferFrom_authorized_spec
    (holder recipient : Address) (amount : Uint256)
    (s s'_direct s'_from : ContractState) : Prop :=
  balanceOf s'_from holder = balanceOf s'_direct holder ∧
  balanceOf s'_from recipient = balanceOf s'_direct recipient ∧
  supply s'_from = supply s'_direct

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
