import Contracts.Common

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Fixed-arity slice of Kleros SortitionTrees.
  The upstream library is dynamic over K and unbounded node arrays; this benchmark
  specializes it to a balanced binary tree with four leaves so the benchmark can
  focus on parent sums, root sums, draw intervals, and index/ID correspondence.
-/
verity_contract SortitionTrees where
  storage
    rootSum : Uint256 := slot 0
    leftSum : Uint256 := slot 1
    rightSum : Uint256 := slot 2
    leaf0 : Uint256 := slot 3
    leaf1 : Uint256 := slot 4
    leaf2 : Uint256 := slot 5
    leaf3 : Uint256 := slot 6
    nodeIndexesToIDs : Uint256 → Uint256 := slot 7
    IDsToNodeIndexes : Uint256 → Uint256 := slot 8
    selectedNode : Uint256 := slot 9

  function setLeaf (nodeIndex : Uint256, stakePathID : Uint256, weight : Uint256) : Unit := do
    require (nodeIndex >= 3) "LeafIndexTooSmall"
    require (nodeIndex <= 6) "LeafIndexTooLarge"

    if nodeIndex == 3 then
      setStorage leaf0 weight
    else if nodeIndex == 4 then
      setStorage leaf1 weight
    else if nodeIndex == 5 then
      setStorage leaf2 weight
    else
      setStorage leaf3 weight

    setMapping nodeIndexesToIDs nodeIndex stakePathID
    setMapping IDsToNodeIndexes stakePathID nodeIndex

    let leaf0Value ← getStorage leaf0
    let leaf1Value ← getStorage leaf1
    let leaf2Value ← getStorage leaf2
    let leaf3Value ← getStorage leaf3

    let nextLeft := add leaf0Value leaf1Value
    let nextRight := add leaf2Value leaf3Value

    setStorage leftSum nextLeft
    setStorage rightSum nextRight
    setStorage rootSum (add nextLeft nextRight)

  function draw (ticket : Uint256) : Uint256 := do
    let root ← getStorage rootSum
    let left ← getStorage leftSum
    let leaf0Value ← getStorage leaf0
    let leaf2Value ← getStorage leaf2

    require (root != 0) "TreeEmpty"
    require (ticket < root) "TicketOutOfRange"

    let selected :=
      if ticket < left then
        if ticket < leaf0Value then 3 else 4
      else
        let rightTicket := sub ticket left
        if rightTicket < leaf2Value then 5 else 6

    setStorage selectedNode selected
    return selected

end Benchmark.Cases.Kleros.SortitionTrees
