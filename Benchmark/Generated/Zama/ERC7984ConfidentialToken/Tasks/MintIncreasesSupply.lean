import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Successful mint increases totalSupply and receiver balance by amount.

When totalSupply + amount does not overflow uint64 (tryIncrease64 succeeds),
minting produces exactly `amount` new tokens: totalSupply increases by amount
and balances[to] increases by amount (mod 2^64).
-/
theorem mint_increases_supply
    (to : Address) (amount : Uint256) (s : ContractState)
    (hTo : (to != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64 (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 to < UINT64_MOD) :
    let s' := ((ERC7984.mint to amount).run s).snd
    mint_increases_supply_spec to amount s s' := by
  have hRecipientNe : to ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  have hRecipientNZ : to ≠ (0 : Address) := by
    simpa [zeroAddress] using hRecipientNe
  have hSuccess : add64 (s.storage 0) amount >= s.storage 0 := by
    by_cases h : add64 (s.storage 0) amount >= s.storage 0
    · exact h
    · unfold tryIncrease64 at hNoOverflow
      simp [h] at hNoOverflow
  have hSuccess' : (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
    simpa [add64, UINT64_MOD] using hSuccess
  unfold mint_increases_supply_spec supply balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
