import Mathlib.Tactic
import TuzaRankFour.Packing

/-!
# Lexicographically saturated packings

The exchange phase in the twelve-vertex reduction may be replaced by one
finite extremal choice: first maximize the packing cardinality, then maximize
the number of vertices covered by the packing.  Such a packing admits none of
the cardinality-increasing or equal-cardinality support-increasing exchanges.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices occurring in a finite family of triangles. -/
def triangleFamilyVertexSupport (P : Finset (Finset V)) : Finset V :=
  P.biUnion id

/-- A maximum packing whose covered vertex set is largest among all maximum
packings. -/
def IsSupportMaximalPacking (G : SimpleGraph V)
    (S : Finset (Finset V)) : Prop :=
  G.IsTrianglePacking S ∧
    S.card = G.trianglePackingNumber ∧
    ∀ ⦃P : Finset (Finset V)⦄, G.IsTrianglePacking P →
      P.card = G.trianglePackingNumber →
      (triangleFamilyVertexSupport P).card ≤
        (triangleFamilyVertexSupport S).card

/-- A packing improves another packing in the lexicographic order used by the
exchange phase. -/
def PackingImproves (G : SimpleGraph V)
    (S P : Finset (Finset V)) : Prop :=
  G.IsTrianglePacking P ∧
    (S.card < P.card ∨
      S.card = P.card ∧
        (triangleFamilyVertexSupport S).card <
          (triangleFamilyVertexSupport P).card)

/-- Every finite graph has a support-maximal maximum triangle packing. -/
theorem exists_supportMaximalPacking (G : SimpleGraph V) :
    ∃ S : Finset (Finset V), G.IsSupportMaximalPacking S := by
  classical
  obtain ⟨P₀, hP₀, hP₀card⟩ := G.exists_max_trianglePacking
  let candidates : Finset (Finset (Finset V)) :=
    Finset.univ.filter fun P ↦
      G.IsTrianglePacking P ∧ P.card = G.trianglePackingNumber
  have hP₀mem : P₀ ∈ candidates := by
    simp [candidates, hP₀, hP₀card]
  have hnonempty : candidates.Nonempty := ⟨P₀, hP₀mem⟩
  obtain ⟨S, hSmem, hmax⟩ := Finset.exists_mem_eq_sup candidates hnonempty
    (fun P ↦ (triangleFamilyVertexSupport P).card)
  have hSdata :
      G.IsTrianglePacking S ∧ S.card = G.trianglePackingNumber := by
    simpa [candidates] using hSmem
  refine ⟨S, hSdata.1, hSdata.2, ?_⟩
  intro P hP hPcard
  have hPmem : P ∈ candidates := by
    simp [candidates, hP, hPcard]
  have hle := Finset.le_sup
    (s := candidates)
    (f := fun Q ↦ (triangleFamilyVertexSupport Q).card) hPmem
  simpa [hmax] using hle

/-- A support-maximal maximum packing admits no lexicographic improvement. -/
theorem not_packingImproves_of_isSupportMaximalPacking
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (hS : G.IsSupportMaximalPacking S) :
    ∀ P : Finset (Finset V), ¬G.PackingImproves S P := by
  intro P hP
  rcases hP with ⟨hPpacking, hcard | ⟨hcard, hsupport⟩⟩
  · have hbound := G.card_le_trianglePackingNumber hPpacking
    have hScard := hS.2.1
    omega
  · have hPcard : P.card = G.trianglePackingNumber := by
      rw [← hS.2.1, ← hcard]
    have hbound := hS.2.2 hPpacking hPcard
    exact (Nat.not_lt_of_ge hbound) hsupport

end SimpleGraph
