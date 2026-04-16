import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/--
Successful burn decreases both sender balance and totalSupply.

When the sender has sufficient balance (fromBalance >= amount), burning
decreases balances[from] by amount and totalSupply by amount.
-/
theorem burn_decreases_supply
    (holder : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hSufficient : s.storageMap 1 holder >= amount)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD) :
    let s' := ((ERC7984.burn holder amount).run s).snd
    burn_decreases_supply_spec holder amount s s' := by
  have hHolderNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  have hHolderNZ : holder ≠ (0 : Address) := by
    simpa [zeroAddress] using hHolderNe
  have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  unfold burn_decreases_supply_spec balanceOf supply
  dsimp
  intro _
  constructor
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
