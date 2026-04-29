# Spec review

Plain-English mapping:
- `price_at_start_time_spec`: at the start of an auction, the per-pair
  price equals the launcher-published `startPrice`.
- `price_at_end_time_spec`: at the end of an auction (when the auction
  is not atomic-swap), the per-pair price equals the launcher-published
  `endPrice`.
- `price_lower_bound_spec`: at any valid timestamp during an auction,
  the per-pair price is at least `endPrice`. This is the floor that
  protects the bidder.
- `price_upper_bound_spec`: at any valid timestamp during an auction,
  the per-pair price is at most `startPrice`. This is the ceiling that
  protects the protocol against extraction.
- `band_well_formed_spec`: helper — `endPrice ≤ startPrice` falls out
  of the input bounds enforced by `openAuction` / `startRebalance`.

Why this matches the intended property:
- Reserve auction launchers publish a price band `[endPrice, startPrice]`
  per pair, derived from per-token `PriceRange { low, high }` quotes
  via `mulDiv(_, D27, _, Ceil)`. The protocol's safety relies on
  `_price` *always* returning a value inside that band, regardless of
  the time-decay branch executed.
- The lower-bound and upper-bound specs together fully capture
  "auction price bounds being respected" as Patrick McKelvy named
  the property in the Telegram brief.
- Boundary exactness is a sanity corollary that ensures no off-by-one
  at the auction edges.

Out of scope (deferred to v2 case):
- Time monotonicity: `t1 ≤ t2 ⟹ price(t1) ≥ price(t2)`. Requires
  `exp` monotonicity in addition to the `≤ D18` axiom and adds
  meaningful proof complexity.
