# auction_price_band

Source:
- `reserve-protocol/dtfs`
- commit `14f75d18856d587adfaff24e77e5b20dda7c7267`
- file `contracts/utils/RebalancingLib.sol`

Focus:
- `_price`
- band invariant: `endPrice ≤ price ≤ startPrice` for every valid timestamp
- boundary exactness: `price(startTime) = startPrice`, `price(endTime) = endPrice`

Out of scope:
- bid-side accounting (`bid`, `getBid`)
- rebalance lifecycle (`startRebalance`, `openAuction`)
- time monotonicity of the price curve (deferred to a v2 case)
- bit-faithful PRBMath semantics — `MathLib.exp` and `MathLib.ln` are axiomatised
