# Upstream metadata

- Repository: https://github.com/Figu3/sonic-earn-recovery-system
- Commit: `699cbbc79def374cab9739e451acbbf866293d12`
- Contract path: `src/StreamRecoveryClaim.sol`
- Primary lines of interest: `claimUsdc`, `_claimUsdc`, `claimWeth`, `_claimWeth`, `claimBoth`
- Source language: Solidity `0.8.24`

Reason for selection:
- narrow, reviewable multi-asset accounting property
- direct fit with the requested "users cannot claim more than their entitlement" goal
- supports a non-interference proof for the combined `claimBoth` entry point
