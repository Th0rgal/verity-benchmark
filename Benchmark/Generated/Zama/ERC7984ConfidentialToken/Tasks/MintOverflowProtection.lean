import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Mint overflow protection: when totalSupply + amount overflows uint64,
no tokens are minted.

FHESafeMath.tryIncrease detects overflow by checking whether
(oldValue + delta) mod 2^64 >= oldValue. On overflow, the wrapped sum
is less than oldValue, so tryIncrease returns (false, oldValue).
Then FHE.select picks 0 as the transferred amount.
-/
theorem mint_overflow_protection
    (to : Address) (amount : Uint256) (s : ContractState)
    (hTo : (to != zeroAddress) = true)
    (hOverflow : (tryIncrease64 (s.storage 0) amount).1 = false)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 to < UINT64_MOD) :
    let s' := ((ERC7984.mint to amount).run s).snd
    mint_overflow_protection_spec to amount s s' := by
  have hRecipientNe : to ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  have hRecipientNZ : to ≠ (0 : Address) := by
    simpa [zeroAddress] using hRecipientNe
  have hFail : ¬ add64 (s.storage 0) amount >= s.storage 0 := by
    intro hSuccess
    have : (tryIncrease64 (s.storage 0) amount).1 = true := by
      simp [tryIncrease64, hSuccess]
    rw [this] at hOverflow
    contradiction
  have hFail' : ¬ (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
    simpa [add64, UINT64_MOD] using hFail
  unfold mint_overflow_protection_spec supply balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
