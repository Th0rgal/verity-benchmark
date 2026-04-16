# Spec review

Plain-English mapping:
- `level2_parent_equals_sum_of_children_spec`: each level-2 node equals the sum of its two leaf children.
- `level1_parent_equals_sum_of_children_spec`: each level-1 node equals the sum of its two level-2 children.
- `root_equals_sum_of_leaves_spec`: the root stores the total stake across all eight leaves.
- `root_minus_left_equals_right_subtree_spec`: root minus left subtree equals right subtree.
- `draw_interval_matches_weights_spec`: ticket intervals assigned by the 3-level draw routine match the leaves' weights.
- `draw_selects_valid_leaf_spec`: any in-range draw must end at one of the eight leaf indices (7..14).
- `node_id_bijection_spec`: node-index and stake-path mappings remain mutually consistent.
- `overflow_safety_spec`: root is at least as large as each level-1 child (conditional on no modular wrap).
- `level1_overflow_safety_spec`: each level-1 node is at least as large as each of its level-2 children (conditional on no modular wrap).
- `remove_leaf_zeroed_spec`: after removeLeaf, the removed leaf has weight zero.
- `remove_leaf_clears_id_spec`: after removeLeaf, ID mappings for the removed node are cleared (requires knowing the previously associated stakePathID).
- `sequential_setLeaf_root_conservation_spec`: after two consecutive setLeaf calls, root still equals sum of all leaves.

Why this matches the intended property:
- The real library's critical behavior is additive parent maintenance plus weighted traversal during draw.
- The 8-leaf, 3-level tree preserves that logic with realistic multi-level propagation.
- The removeLeaf function and sequential invariant test properties critical to production usage.

Note on zero-weight exclusion:
- A separate "draw never selects a zero-weight leaf" spec was considered but dropped.
  The naive statement is not provable without root-consistency assumptions (a counterexample
  exists where parent-child sums are correct but the root is inflated, allowing draw to land
  on a zero-weight leaf). The property is already implied by the composition of
  `root_equals_sum_of_leaves` and `draw_interval_matches_weights`: after any `setLeaf`, the
  tree is fully consistent and every zero-weight leaf has a zero-width ticket interval.

Known uncertainties:
- The benchmark specializes the dynamic tree into a fixed binary shape (8 leaves instead of unbounded).
- The probabilistic claim is represented as interval ownership, not as an external probability theorem.
- Overflow specs are conditional on the mathematical sum fitting in 256 bits (modular `add` wraps otherwise).
