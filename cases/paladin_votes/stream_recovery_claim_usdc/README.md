# stream_recovery_claim_usdc

Source:
- `Figu3/sonic-earn-recovery-system`
- commit `699cbbc79def374cab9739e451acbbf866293d12`
- file `src/StreamRecoveryClaim.sol`

Focus:
- `claimUsdc`
- `_claimUsdc`
- `claimWeth`
- `_claimWeth`
- `claimBoth`
- per-token claim accounting, revert safety, and cross-token non-interference

Out of scope:
- multi-round batching
- Merkle proof details
- ERC20 transfer semantics
