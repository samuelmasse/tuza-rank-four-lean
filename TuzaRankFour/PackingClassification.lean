import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import TuzaRankFour.Relabeling

/-!
# Classification of four edge-disjoint triangles

The isomorphism type of four pairwise edge-disjoint triangles is determined
by the non-singleton incidence sets of their vertices.  This file isolates
that finite classification from the graph-theoretic and SAT arguments.
-/

namespace TuzaRankFour.PackingClassification

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev Block := Fin 4
abbrev Mask := Finset Block
abbrev SharedFamily := Finset Mask

/-- The sixteen canonical ordered four-packings used by the finite endpoint.
The outer index agrees with the frozen skeleton index. -/
def canonicalPackings : List (List (List Nat)) :=
  [ [[0, 1, 3], [0, 2, 4], [1, 2, 5], [3, 4, 5]],
    [[0, 1, 3], [0, 2, 4], [1, 2, 5], [3, 4, 6]],
    [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 3, 6]],
    [[0, 1, 3], [0, 2, 4], [1, 2, 5], [3, 6, 7]],
    [[0, 1, 4], [0, 2, 5], [1, 3, 6], [2, 3, 7]],
    [[0, 1, 3], [0, 2, 4], [1, 2, 5], [2, 6, 7]],
    [[0, 1, 3], [0, 2, 4], [1, 2, 5], [6, 7, 8]],
    [[0, 1, 2], [0, 3, 4], [1, 5, 6], [2, 7, 8]],
    [[0, 1, 3], [0, 2, 4], [1, 5, 6], [2, 7, 8]],
    [[0, 1, 2], [0, 3, 4], [1, 5, 6], [1, 7, 8]],
    [[0, 1, 2], [0, 3, 4], [0, 5, 6], [0, 7, 8]],
    [[0, 1, 2], [0, 3, 4], [1, 5, 6], [7, 8, 9]],
    [[0, 2, 3], [0, 4, 5], [1, 6, 7], [1, 8, 9]],
    [[0, 1, 2], [0, 3, 4], [0, 5, 6], [7, 8, 9]],
    [[0, 1, 2], [0, 3, 4], [5, 6, 7], [8, 9, 10]],
    [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]] ]

theorem canonicalPackings_length : canonicalPackings.length = 16 := by decide

/-- Triangle `i` in canonical skeleton `s`, represented on natural labels. -/
def canonicalBlock (s : Fin 16) (i : Block) : Finset Nat :=
  ((canonicalPackings.getD s.val []).getD i.val []).toFinset

/-- Incidence mask of a natural vertex in a canonical packing. -/
def canonicalMask (s : Fin 16) (v : Nat) : Mask :=
  Finset.univ.filter fun i => v ∈ canonicalBlock s i

/-- The non-singleton incidence masks of a canonical packing. -/
def canonicalSharedFamily (s : Fin 16) : SharedFamily :=
  (Finset.range 12).image (canonicalMask s) |>.filter fun m => 2 ≤ m.card

/-- The elementary constraints on shared incidence masks forced by four
three-element blocks with pairwise intersections of size at most one. -/
def Valid (F : SharedFamily) : Prop :=
  (∀ m ∈ F, 2 ≤ m.card) ∧
  (∀ i : Block, (F.filter fun m => i ∈ m).card ≤ 3) ∧
  (∀ i j : Block, i = j ∨
    (F.filter fun m => i ∈ m ∧ j ∈ m).card ≤ 1)

def validBool (F : SharedFamily) : Bool :=
  decide ((F.filter fun m => decide (m.card < 2)) = ∅) &&
  decide (((Finset.univ : Finset Block).filter fun i =>
    decide (3 < (F.filter fun m => i ∈ m).card)) = ∅) &&
  decide ((((Finset.univ : Finset (Block × Block)).filter fun ij =>
    decide (ij.1 ≠ ij.2 ∧
      1 < (F.filter fun m => ij.1 ∈ m ∧ ij.2 ∈ m).card))) = ∅)

theorem validBool_eq_true_iff (F : SharedFamily) :
    validBool F = true ↔ Valid F := by
  simp only [validBool, Bool.and_eq_true, decide_eq_true_eq,
    Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
    not_lt, not_and_or, not_ne_iff, Valid]
  constructor
  · rintro ⟨⟨hMasks, hDegree⟩, hPairs⟩
    exact ⟨fun m hm => hMasks hm, fun i => hDegree (x := i),
      fun i j => hPairs (x := (i, j))⟩
  · rintro ⟨hMasks, hDegree, hPairs⟩
    refine ⟨⟨fun _ hm => hMasks _ hm, fun _ => hDegree _⟩, ?_⟩
    rintro ⟨i, j⟩
    exact hPairs i j

/-- The eleven possible non-singleton masks on four blocks. -/
def sharedMasks : Finset Mask :=
  Finset.univ.filter fun m => 2 ≤ m.card

/-- Relabel the four blocks of a shared-incidence family. -/
def permuteFamily (p : Equiv.Perm Block) (F : SharedFamily) : SharedFamily :=
  F.map p.finsetCongr.toEmbedding

/-- Three masks used only to divide the finite check into balanced pieces. -/
def shardMask0 : Mask := {0, 1, 2, 3}
def shardMask1 : Mask := {0, 1, 2}
def shardMask2 : Mask := {0, 1, 3}

/-- Three membership bits give a balanced shard key. -/
def shardKey (F : SharedFamily) : Fin 8 :=
  ⟨(if shardMask0 ∈ F then 4 else 0) +
    (if shardMask1 ∈ F then 2 else 0) +
    (if shardMask2 ∈ F then 1 else 0), by
      split_ifs <;> omega⟩

/-- One of eight disjoint, memory-safe pieces of the 2,048-candidate search. -/
def candidateShard (k : Fin 8) : Finset SharedFamily :=
  sharedMasks.powerset.filter fun F => shardKey F = k

/-- The eight shards cover the whole candidate powerset. -/
theorem mem_candidateShard (F : SharedFamily) (hF : F ∈ sharedMasks.powerset) :
    ∃ k : Fin 8, F ∈ candidateShard k := by
  exact ⟨shardKey F, by simp [candidateShard, hF]⟩

end TuzaRankFour.PackingClassification
