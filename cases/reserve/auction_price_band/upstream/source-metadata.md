# Upstream metadata

- Repository: https://github.com/reserve-protocol/dtfs
- Commit: `14f75d18856d587adfaff24e77e5b20dda7c7267`
- Contract path: `contracts/utils/RebalancingLib.sol`
- Function of interest: `_price` (lines 427-475)
- Source language: Solidity

Reason for selection:
- Per Reserve protocol engineers (Patrick McKelvy / akshat / tbrent),
  the highest-priority invariants are around auction-time accounting,
  specifically auction price bounds being respected.
- `_price` is the per-pair price oracle for every `bid` in the
  protocol; if it returns a value outside `[endPrice, startPrice]`
  during an auction, basket value is extractable.
- Real production exponential-decay arithmetic mediated by PRBMath's
  `UD60x18.ln` and `SD59x18.exp` — exercises the kind of fixed-point
  axiomatic boundary that other Verity cases (Cork, Lido) sidestep.
