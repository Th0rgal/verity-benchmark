# Upstream metadata

- Repository: https://github.com/safe-global/safe-smart-account
- Branch: `main`
- Commit: `a2e19c6aa42a45ceec68057f3fa387f169c5b321`
- Contract path: `contracts/base/OwnerManager.sol`
- Functions of interest: `addOwnerWithThreshold`
- Source language: Solidity ^0.7.0
- Certora spec: `certora/specs/OwnerReach.spec`

Reason for selection:
- The Certora OwnerReach.spec defines a set of invariants over the owners
  linked list using ghost variables and reachability predicates
- The `inListReachable` invariant requires proving that every node with a
  non-zero successor is reachable from the SENTINEL node
- This is a structural linked list property requiring witness-based reasoning
  rather than pure arithmetic, complementing the arithmetic-focused Lido case
- The proof technique (chain lifting + prepending) is representative of
  data structure invariant proofs in smart contract verification
