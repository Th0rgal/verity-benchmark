import Contracts.Common

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Fixed-arity slice of Kleros SortitionTrees.
  The upstream library is dynamic over K and unbounded node arrays; this benchmark
  specializes it to a balanced binary tree with **eight leaves** (three levels) so the
  benchmark can exercise multi-level parent propagation, draw traversal depth, and
  removal semantics in addition to the original conservation and selection properties.

  Tree layout (indices = storage slot numbers):

              rootSum (0)
             /            \
        node1 (1)       node2 (2)
        /      \        /      \
    node3 (3) node4 (4) node5 (5) node6 (6)
    / \       / \       / \       / \
  L0  L1   L2  L3    L4  L5    L6  L7
  (7) (8)  (9)(10)  (11)(12)  (13)(14)

  Slots 15-16: bidirectional ID mappings
  Slot 17: selectedNode (draw result)
-/
verity_contract SortitionTrees where
  storage
    rootSum   : Uint256 := slot 0
    node1     : Uint256 := slot 1
    node2     : Uint256 := slot 2
    node3     : Uint256 := slot 3
    node4     : Uint256 := slot 4
    node5     : Uint256 := slot 5
    node6     : Uint256 := slot 6
    leaf0     : Uint256 := slot 7
    leaf1     : Uint256 := slot 8
    leaf2     : Uint256 := slot 9
    leaf3     : Uint256 := slot 10
    leaf4     : Uint256 := slot 11
    leaf5     : Uint256 := slot 12
    leaf6     : Uint256 := slot 13
    leaf7     : Uint256 := slot 14
    nodeIndexesToIDs : Uint256 → Uint256 := slot 15
    IDsToNodeIndexes : Uint256 → Uint256 := slot 16
    selectedNode : Uint256 := slot 17

  function setLeaf (nodeIndex : Uint256, stakePathID : Uint256, weight : Uint256) : Unit := do
    require (nodeIndex >= 7)  "LeafIndexTooSmall"
    require (nodeIndex <= 14) "LeafIndexTooLarge"

    -- Read all current leaves
    let l0 ← getStorage leaf0
    let l1 ← getStorage leaf1
    let l2 ← getStorage leaf2
    let l3 ← getStorage leaf3
    let l4 ← getStorage leaf4
    let l5 ← getStorage leaf5
    let l6 ← getStorage leaf6
    let l7 ← getStorage leaf7

    -- Update the targeted leaf
    let nl0 := ite (nodeIndex == 7)  weight l0
    let nl1 := ite (nodeIndex == 8)  weight l1
    let nl2 := ite (nodeIndex == 9)  weight l2
    let nl3 := ite (nodeIndex == 10) weight l3
    let nl4 := ite (nodeIndex == 11) weight l4
    let nl5 := ite (nodeIndex == 12) weight l5
    let nl6 := ite (nodeIndex == 13) weight l6
    let nl7 := ite (nodeIndex == 14) weight l7

    -- Write all leaves
    setStorage leaf0 nl0
    setStorage leaf1 nl1
    setStorage leaf2 nl2
    setStorage leaf3 nl3
    setStorage leaf4 nl4
    setStorage leaf5 nl5
    setStorage leaf6 nl6
    setStorage leaf7 nl7

    -- Update ID mappings
    setMappingUint nodeIndexesToIDs nodeIndex stakePathID
    setMappingUint IDsToNodeIndexes stakePathID nodeIndex

    -- Propagate sums: level 2 (grandparents of leaves)
    let nextNode3 := add nl0 nl1
    let nextNode4 := add nl2 nl3
    let nextNode5 := add nl4 nl5
    let nextNode6 := add nl6 nl7

    setStorage node3 nextNode3
    setStorage node4 nextNode4
    setStorage node5 nextNode5
    setStorage node6 nextNode6

    -- Propagate sums: level 1
    let nextNode1 := add nextNode3 nextNode4
    let nextNode2 := add nextNode5 nextNode6

    setStorage node1 nextNode1
    setStorage node2 nextNode2

    -- Propagate sums: root
    setStorage rootSum (add nextNode1 nextNode2)

  function removeLeaf (nodeIndex : Uint256) : Unit := do
    require (nodeIndex >= 7)  "LeafIndexTooSmall"
    require (nodeIndex <= 14) "LeafIndexTooLarge"

    -- Look up the stake-path ID before clearing
    let stakePathID ← getMappingUint nodeIndexesToIDs nodeIndex

    -- Read all current leaves
    let l0 ← getStorage leaf0
    let l1 ← getStorage leaf1
    let l2 ← getStorage leaf2
    let l3 ← getStorage leaf3
    let l4 ← getStorage leaf4
    let l5 ← getStorage leaf5
    let l6 ← getStorage leaf6
    let l7 ← getStorage leaf7

    -- Zero out the targeted leaf
    let nl0 := ite (nodeIndex == 7)  0 l0
    let nl1 := ite (nodeIndex == 8)  0 l1
    let nl2 := ite (nodeIndex == 9)  0 l2
    let nl3 := ite (nodeIndex == 10) 0 l3
    let nl4 := ite (nodeIndex == 11) 0 l4
    let nl5 := ite (nodeIndex == 12) 0 l5
    let nl6 := ite (nodeIndex == 13) 0 l6
    let nl7 := ite (nodeIndex == 14) 0 l7

    -- Write all leaves
    setStorage leaf0 nl0
    setStorage leaf1 nl1
    setStorage leaf2 nl2
    setStorage leaf3 nl3
    setStorage leaf4 nl4
    setStorage leaf5 nl5
    setStorage leaf6 nl6
    setStorage leaf7 nl7

    -- Clear ID mappings
    setMappingUint nodeIndexesToIDs nodeIndex 0
    setMappingUint IDsToNodeIndexes stakePathID 0

    -- Propagate sums: level 2
    let nextNode3 := add nl0 nl1
    let nextNode4 := add nl2 nl3
    let nextNode5 := add nl4 nl5
    let nextNode6 := add nl6 nl7

    setStorage node3 nextNode3
    setStorage node4 nextNode4
    setStorage node5 nextNode5
    setStorage node6 nextNode6

    -- Propagate sums: level 1
    let nextNode1 := add nextNode3 nextNode4
    let nextNode2 := add nextNode5 nextNode6

    setStorage node1 nextNode1
    setStorage node2 nextNode2

    -- Propagate sums: root
    setStorage rootSum (add nextNode1 nextNode2)

  function draw (ticket : Uint256) : Uint256 := do
    let root  ← getStorage rootSum
    let n1    ← getStorage node1
    let n3    ← getStorage node3
    let n5    ← getStorage node5
    let l0Val ← getStorage leaf0
    let l2Val ← getStorage leaf2
    let l4Val ← getStorage leaf4
    let l6Val ← getStorage leaf6

    require (root != 0) "TreeEmpty"
    require (ticket < root) "TicketOutOfRange"

    -- Level 1: left vs right subtree
    -- All sub-expressions are inlined to avoid let-in-ite (#1003)
    let selected :=
      ite (ticket < n1)
        (ite (ticket < n3)
           (ite (ticket < l0Val) 7 8)
           (ite (sub ticket n3 < l2Val) 9 10))
        (ite (sub ticket n1 < n5)
           (ite (sub ticket n1 < l4Val) 11 12)
           (ite (sub (sub ticket n1) n5 < l6Val) 13 14))

    setStorage selectedNode selected
    return selected

end Benchmark.Cases.Kleros.SortitionTrees
