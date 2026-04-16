# sortition_trees

Source:
- `kleros/kleros-v2`
- commit `75125dfa54eee723cac239f20e5746d15786196b`
- file `contracts/src/libraries/SortitionTrees.sol`

Focus:
- `set` (modeled as `setLeaf`)
- `updateParents` (inlined in `setLeaf`)
- `draw`
- `removeLeaf` (new: sets weight to zero and clears ID mappings)
- multi-level parent propagation, root conservation, draw intervals, ID/index consistency
- overflow safety, sequential operation invariants

Tree layout (8 leaves, 3 levels):

```
            rootSum (0)
           /            \
      node1 (1)       node2 (2)
      /      \        /      \
  node3 (3) node4 (4) node5 (5) node6 (6)
  / \       / \       / \       / \
L0  L1   L2  L3    L4  L5    L6  L7
(7) (8)  (9)(10)  (11)(12)  (13)(14)
```

Out of scope:
- dynamic branching factor
- bytes32 packing
- ticket hashing
- vacancy-stack details (removeLeaf is simplified to zero-weight + mapping clear)
