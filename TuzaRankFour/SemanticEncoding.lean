import Mathlib.Data.Finset.Sort
import TuzaRankFour.FiniteEncoding
import TuzaRankFour.Reduction
import TuzaRankFour.SmallRanks

/-!
# Semantics of the finite rank-four formulas

The LRAT files prove that the frozen DIMACS formulas are inconsistent.  This
module supplies the independent mathematical side of that interface: it
reconstructs the base clauses and the two kinds of semantic cuts from compact
combinatorial witnesses.
-/

namespace TuzaRankFour.SemanticEncoding

open TuzaRankFour.FiniteEncoding

deriving instance DecidableEq for Sat.Literal

/-- A literal is true under a valuation in the usual propositional sense. -/
def literalTrue (v : Sat.Valuation) : Sat.Literal → Prop
  | .pos i => v i
  | .neg i => ¬v i

/-- Mathlib's continuation-style clause semantics agrees with the usual
existence of a true literal. -/
theorem satisfies_iff_exists_literalTrue (v : Sat.Valuation) (c : Sat.Clause) :
    v.satisfies c ↔ ∃ l, List.Mem l c ∧ literalTrue v l := by
  classical
  induction c with
  | nil =>
      constructor
      · intro h
        exact h.elim
      · rintro ⟨l, hmem, _⟩
        exact nomatch hmem
  | cons l c ih =>
      cases l with
      | pos i =>
          constructor
          · intro h
            by_cases hi : v i
            · exact ⟨.pos i, .head c, hi⟩
            · obtain ⟨l, hl, htrue⟩ := ih.mp (h hi)
              exact ⟨l, .tail _ hl, htrue⟩
          · rintro ⟨l, hl, htrue⟩ hi
            rcases List.mem_cons.mp hl with rfl | hl
            · exact (hi htrue).elim
            · exact ih.mpr ⟨l, hl, htrue⟩
      | neg i =>
          constructor
          · intro h
            by_cases hi : v i
            · obtain ⟨l, hl, htrue⟩ := ih.mp (h hi)
              exact ⟨l, .tail _ hl, htrue⟩
            · exact ⟨.neg i, .head c, hi⟩
          · rintro ⟨l, hl, htrue⟩ hi
            rcases List.mem_cons.mp hl with rfl | hl
            · exact (htrue hi).elim
            · exact ih.mpr ⟨l, hl, htrue⟩

/-- The three normalized graph edges of an ordered vertex triple. -/
def triangleEdges {n : Nat} (t : Fin n × Fin n × Fin n) :
    List (Fin n × Fin n) :=
  [(t.1, t.2.1), (t.1, t.2.2), (t.2.1, t.2.2)]

/-- Turn a normalized endpoint pair into the corresponding two-set. -/
def edgeFinset {n : Nat} (e : Fin n × Fin n) : Finset (Fin n) :=
  {e.1, e.2}

/-- Turn an ordered vertex triple into the corresponding three-set. -/
def triangleFinset {n : Nat} (t : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {t.1, t.2.1, t.2.2}

/-- Zero-based propositional variable of a triangle index. -/
def triangleVariable (n index : Nat) : Nat := edgeVariableCount n + index

/-- Zero-based propositional variable of a normalized graph edge. -/
def edgeVariable {n : Nat} (e : Fin n × Fin n) : Nat :=
  (orderedEdges n).idxOf e

theorem mem_orderedEdges_iff {n : Nat} {i j : Fin n} :
    (i, j) ∈ orderedEdges n ↔ i < j := by
  simp [orderedEdges]

theorem mem_orderedTriangles_iff {n : Nat} {i j k : Fin n} :
    (i, j, k) ∈ orderedTriangles n ↔ i < j ∧ j < k := by
  simp [orderedTriangles]

theorem triangleEdges_mem_orderedEdges {n : Nat}
    {t : Fin n × Fin n × Fin n} (ht : t ∈ orderedTriangles n) :
    ∀ e ∈ triangleEdges t, e ∈ orderedEdges n := by
  obtain ⟨hij, hjk⟩ := mem_orderedTriangles_iff.mp ht
  intro e he
  simp only [triangleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact mem_orderedEdges_iff.mpr hij
  · exact mem_orderedEdges_iff.mpr (hij.trans hjk)
  · exact mem_orderedEdges_iff.mpr hjk

theorem graphValuation_edge_at {n : Nat} (G : SimpleGraph (Fin n))
    {i : Nat} {e : Fin n × Fin n}
    (hget : (orderedEdges n)[i]? = some e) :
    graphValuation G i ↔ G.Adj e.1 e.2 := by
  unfold graphValuation
  rw [hget]

theorem graphValuation_edgeVariable {n : Nat} (G : SimpleGraph (Fin n))
    {e : Fin n × Fin n} (he : e ∈ orderedEdges n) :
    graphValuation G (edgeVariable e) ↔ G.Adj e.1 e.2 := by
  exact graphValuation_edge_at G (List.getElem?_idxOf he)

theorem graphValuation_triangle_at {n : Nat} (G : SimpleGraph (Fin n))
    {i : Nat} {t : Fin n × Fin n × Fin n}
    (hget : (orderedTriangles n)[i]? = some t) :
    graphValuation G (triangleVariable n i) ↔
      G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2 := by
  unfold graphValuation triangleVariable
  have hedge : (orderedEdges n)[edgeVariableCount n + i]? = none := by
    rw [List.getElem?_eq_none]
    simp [edgeVariableCount]
  rw [hedge]
  simp only [edgeVariableCount, Nat.add_sub_cancel_left]
  rw [hget]

theorem graphValuation_triangle_idxOf {n : Nat} (G : SimpleGraph (Fin n))
    {t : Fin n × Fin n × Fin n} (ht : t ∈ orderedTriangles n) :
    graphValuation G (triangleVariable n ((orderedTriangles n).idxOf t)) ↔
      G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2 := by
  exact graphValuation_triangle_at G (List.getElem?_idxOf ht)

theorem triangleFinset_mem_triangles_iff {n : Nat} (G : SimpleGraph (Fin n))
    {t : Fin n × Fin n × Fin n} (ht : t ∈ orderedTriangles n) :
    triangleFinset t ∈ G.triangles ↔
      G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2 := by
  classical
  obtain ⟨hij, hjk⟩ := mem_orderedTriangles_iff.mp ht
  constructor
  · intro htriangle
    have hclique : G.IsNClique 3 (triangleFinset t) := by
      simpa [SimpleGraph.triangles] using htriangle
    refine ⟨hclique.isClique (by simp [triangleFinset])
      (by simp [triangleFinset]) hij.ne, ?_, ?_⟩
    · exact hclique.isClique (by simp [triangleFinset])
        (by simp [triangleFinset]) (hij.trans hjk).ne
    · exact hclique.isClique (by simp [triangleFinset])
        (by simp [triangleFinset]) hjk.ne
  · rintro ⟨hijAdj, hikAdj, hjkAdj⟩
    simp only [SimpleGraph.triangles, SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · intro u hu v hv huv
      simp [triangleFinset] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      all_goals first | exact (huv rfl).elim | assumption | exact hijAdj.symm |
        exact hikAdj.symm | exact hjkAdj.symm
    · simp [triangleFinset, hij.ne, hjk.ne, (hij.trans hjk).ne]

/-- Every three-set of labelled vertices has a unique increasing tuple
representation in the DIMACS triangle order. -/
theorem exists_orderedTriangle_of_card_eq_three {n : Nat}
    (s : Finset (Fin n)) (hcard : s.card = 3) :
    ∃ t ∈ orderedTriangles n, triangleFinset t = s := by
  classical
  let e : Fin 3 ≃o s := s.orderIsoOfFin hcard
  let i : Fin n := (e 0).val
  let j : Fin n := (e 1).val
  let k : Fin n := (e 2).val
  have hij : i < j := by
    exact_mod_cast e.lt_iff_lt.mpr (by decide : (0 : Fin 3) < 1)
  have hjk : j < k := by
    exact_mod_cast e.lt_iff_lt.mpr (by decide : (1 : Fin 3) < 2)
  refine ⟨(i, j, k), mem_orderedTriangles_iff.mpr ⟨hij, hjk⟩, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp [triangleFinset] at hx
    rcases hx with rfl | rfl | rfl
    · exact (e 0).property
    · exact (e 1).property
    · exact (e 2).property
  · simp [triangleFinset, hij.ne, hjk.ne, (hij.trans hjk).ne, hcard]

/-- For normalized tuples, containment of the two-set is equivalent to
membership in the tuple's explicit edge list. -/
theorem mem_triangleEdges_iff_edgeFinset_subset {n : Nat}
    {e : Fin n × Fin n} {t : Fin n × Fin n × Fin n}
    (he : e ∈ orderedEdges n) (ht : t ∈ orderedTriangles n) :
    e ∈ triangleEdges t ↔ edgeFinset e ⊆ triangleFinset t := by
  obtain hij := mem_orderedEdges_iff.mp he
  obtain ⟨hab, hbc⟩ := mem_orderedTriangles_iff.mp ht
  constructor
  · intro hmem
    simp only [triangleEdges, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp [edgeFinset, triangleFinset]
  · intro hsub
    have hfirst : e.1 ∈ triangleFinset t :=
      hsub (by simp [edgeFinset])
    have hsecond : e.2 ∈ triangleFinset t :=
      hsub (by simp [edgeFinset])
    have hfirst' : e.1 = t.1 ∨ e.1 = t.2.1 ∨ e.1 = t.2.2 := by
      simpa [triangleFinset] using hfirst
    have hsecond' : e.2 = t.1 ∨ e.2 = t.2.1 ∨ e.2 = t.2.2 := by
      simpa [triangleFinset] using hsecond
    rcases hfirst' with h11 | h12 | h13
    · rcases hsecond' with h21 | h22 | h23
      · exact (ne_of_lt hij) (h11.trans h21.symm) |>.elim
      · have hep : e = (t.1, t.2.1) := Prod.ext h11 h22
        simpa [triangleEdges, hep]
      · have hep : e = (t.1, t.2.2) := Prod.ext h11 h23
        simpa [triangleEdges, hep]
    · rcases hsecond' with h21 | h22 | h23
      · have hbad : t.2.1 < t.1 := h12.symm ▸ h21.symm ▸ hij
        exact (not_lt_of_ge hab.le hbad).elim
      · exact (ne_of_lt hij) (h12.trans h22.symm) |>.elim
      · have hep : e = (t.2.1, t.2.2) := Prod.ext h12 h23
        simpa [triangleEdges, hep]
    · rcases hsecond' with h21 | h22 | h23
      · have hbad : t.2.2 < t.1 := h13.symm ▸ h21.symm ▸ hij
        exact (not_lt_of_ge (hab.trans hbc).le hbad).elim
      · have hbad : t.2.2 < t.2.1 := h13.symm ▸ h22.symm ▸ hij
        exact (not_lt_of_ge hbc.le hbad).elim
      · exact (ne_of_lt hij) (h13.trans h23.symm) |>.elim

/-- Decode a list of zero-based triangle indices.  Out-of-range indices are
discarded; validity below rules them out for packing cuts. -/
def decodeTriangles (n : Nat) (indices : List Nat) :
    List (Fin n × Fin n × Fin n) :=
  indices.filterMap fun i => (orderedTriangles n)[i]?

/-- Decode a list of zero-based edge indices. -/
def decodeEdges (n : Nat) (indices : List Nat) : List (Fin n × Fin n) :=
  indices.filterMap fun i => (orderedEdges n)[i]?

/-- The edge sets used by a decoded triangle. -/
def triangleEdgeFinsets {n : Nat} (t : Fin n × Fin n × Fin n) :
    Finset (Finset (Fin n)) :=
  (triangleEdges t).toFinset.image edgeFinset

/-- A compact witness for one learned semantic clause. -/
inductive Cut where
  | packing (triangleIndices : List Nat)
  | cover (edgeIndices : List Nat)
  deriving Repr, DecidableEq

/-- Boolean test that two decoded triangles share no graph edge. -/
def edgeDisjointBool {n : Nat} (s t : Fin n × Fin n × Fin n) : Bool :=
  decide ((triangleFinset s ∩ triangleFinset t).card ≤ 1)

/-- Boolean pairwise edge-disjointness test for a triangle list. -/
def pairwiseEdgeDisjointBool {n : Nat} :
    List (Fin n × Fin n × Fin n) → Bool
  | [] => true
  | t :: ts => ts.all (edgeDisjointBool t) && pairwiseEdgeDisjointBool ts

/-- A packing witness is valid when it decodes to five triples whose graph
edge sets are pairwise disjoint. -/
def packingValidBool (n : Nat) (indices : List Nat) : Bool :=
  let ts := decodeTriangles n indices
  ts.length == 5 && pairwiseEdgeDisjointBool ts

theorem pairwiseEdgeDisjointBool_eq_true_iff {n : Nat}
    (ts : List (Fin n × Fin n × Fin n)) :
    pairwiseEdgeDisjointBool ts = true ↔
      ts.Pairwise fun s t => (triangleFinset s ∩ triangleFinset t).card ≤ 1 := by
  induction ts with
  | nil => simp [pairwiseEdgeDisjointBool]
  | cons t ts ih =>
      simp only [pairwiseEdgeDisjointBool, Bool.and_eq_true, ih,
        List.pairwise_cons]
      constructor
      · rintro ⟨hall, hpair⟩
        refine ⟨?_, hpair⟩
        intro s hs
        have := List.all_eq_true.mp hall s hs
        simpa [edgeDisjointBool] using of_decide_eq_true this
      · rintro ⟨hall, hpair⟩
        refine ⟨List.all_eq_true.mpr ?_, hpair⟩
        intro s hs
        simp [edgeDisjointBool, hall s hs]

theorem packingValidBool_eq_true_iff (n : Nat) (indices : List Nat) :
    packingValidBool n indices = true ↔
      let ts := decodeTriangles n indices
      ts.length = 5 ∧
        ts.Pairwise fun s t =>
          (triangleFinset s ∩ triangleFinset t).card ≤ 1 := by
  simp [packingValidBool, pairwiseEdgeDisjointBool_eq_true_iff]

def PackingValid (n : Nat) (indices : List Nat) : Prop :=
  packingValidBool n indices = true

theorem mem_decodeTriangles {n : Nat} {indices : List Nat}
    {t : Fin n × Fin n × Fin n} (ht : t ∈ decodeTriangles n indices) :
    ∃ i ∈ indices, (orderedTriangles n)[i]? = some t := by
  simpa [decodeTriangles] using List.mem_filterMap.mp ht

theorem decodeTriangle_mem_orderedTriangles {n : Nat} {indices : List Nat}
    {t : Fin n × Fin n × Fin n} (ht : t ∈ decodeTriangles n indices) :
    t ∈ orderedTriangles n := by
  obtain ⟨i, -, hi⟩ := mem_decodeTriangles ht
  exact List.mem_iff_getElem?.mpr ⟨i, hi⟩

theorem mem_decodeEdges {n : Nat} {indices : List Nat}
    {e : Fin n × Fin n} (he : e ∈ decodeEdges n indices) :
    ∃ i ∈ indices, (orderedEdges n)[i]? = some e := by
  simpa [decodeEdges] using List.mem_filterMap.mp he

theorem decodeEdge_mem_orderedEdges {n : Nat} {indices : List Nat}
    {e : Fin n × Fin n} (he : e ∈ decodeEdges n indices) :
    e ∈ orderedEdges n := by
  obtain ⟨i, -, hi⟩ := mem_decodeEdges he
  exact List.mem_iff_getElem?.mpr ⟨i, hi⟩

theorem triangleFinset_card_of_mem_orderedTriangles {n : Nat}
    {t : Fin n × Fin n × Fin n} (ht : t ∈ orderedTriangles n) :
    (triangleFinset t).card = 3 := by
  obtain ⟨hij, hjk⟩ := mem_orderedTriangles_iff.mp ht
  simp [triangleFinset, hij.ne, hjk.ne, (hij.trans hjk).ne]

theorem edgeFinset_card_of_mem_orderedEdges {n : Nat}
    {e : Fin n × Fin n} (he : e ∈ orderedEdges n) :
    (edgeFinset e).card = 2 := by
  have hij := mem_orderedEdges_iff.mp he
  simp [edgeFinset, hij.ne]

private theorem map_triangleFinset_nodup_of_pairwise {n : Nat}
    (ts : List (Fin n × Fin n × Fin n))
    (hordered : ∀ t ∈ ts, t ∈ orderedTriangles n)
    (hpair : ts.Pairwise fun s t =>
      (triangleFinset s ∩ triangleFinset t).card ≤ 1) :
    (ts.map triangleFinset).Nodup := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [List.pairwise_cons] at hpair
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro htmem
        obtain ⟨u, hu, heq⟩ := List.mem_map.mp htmem
        have hle := hpair.1 u hu
        have htcard := triangleFinset_card_of_mem_orderedTriangles
          (hordered t (by simp))
        rw [heq, Finset.inter_self, htcard] at hle
        omega
      · apply ih
        · intro u hu
          exact hordered u (by simp [hu])
        · exact hpair.2

/-- A rank-at-most-four graph cannot make all literals of a valid five-
triangle packing witness true. -/
theorem graphValuation_noFive {n : Nat} (G : SimpleGraph (Fin n))
    (hν : G.trianglePackingNumber ≤ 4) :
    ∀ indices, PackingValid n indices →
      ¬∀ i ∈ indices, graphValuation G (triangleVariable n i) := by
  classical
  intro indices hvalid hall
  let ts := decodeTriangles n indices
  obtain ⟨hlen, hpair⟩ :=
    (packingValidBool_eq_true_iff n indices).mp hvalid
  have hordered : ∀ t ∈ ts, t ∈ orderedTriangles n := by
    intro t ht
    exact decodeTriangle_mem_orderedTriangles ht
  let P : Finset (Finset (Fin n)) := (ts.map triangleFinset).toFinset
  have hnodup : (ts.map triangleFinset).Nodup :=
    map_triangleFinset_nodup_of_pairwise ts hordered hpair
  have hPcard : P.card = 5 := by
    rw [show P = (ts.map triangleFinset).toFinset by rfl,
      List.toFinset_card_of_nodup hnodup, List.length_map, hlen]
  have hpacking : G.IsTrianglePacking P := by
    constructor
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
      obtain ⟨i, hi, hget⟩ := mem_decodeTriangles ht
      have htrue := hall i hi
      exact (triangleFinset_mem_triangles_iff G (hordered t ht)).mpr
        ((graphValuation_triangle_at G hget).mp htrue)
    · intro s hs t ht hst
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      letI : Std.Symm (fun a b : Fin n × Fin n × Fin n =>
          (triangleFinset a ∩ triangleFinset b).card ≤ 1) :=
        ⟨by
          intro a b hab
          simpa [Finset.inter_comm] using hab⟩
      exact hpair.forall hs' ht' (by
        intro heq
        exact hst (congrArg triangleFinset heq))
  have hfive : 5 ≤ G.trianglePackingNumber := by
    simpa [hPcard] using G.card_le_trianglePackingNumber hpacking
  omega

/-- A cover witness is valid when its decoded edge list has length at most
eight.  Duplicates are harmless and only make the resulting cover smaller. -/
def coverValidBool (n : Nat) (indices : List Nat) : Bool :=
  decide ((decodeEdges n indices).length ≤ 8)

def CoverValid (n : Nat) (indices : List Nat) : Prop :=
  coverValidBool n indices = true

/-- Every witness in a cut stream is locally well formed. -/
def Cut.Valid (n : Nat) : Cut → Prop
  | .packing indices => PackingValid n indices
  | .cover indices => CoverValid n indices

/-- Executable local-validity test used by the compact witness importer. -/
def Cut.validBool (n : Nat) : Cut → Bool
  | .packing indices => packingValidBool n indices
  | .cover indices => coverValidBool n indices

theorem Cut.validBool_eq_true_iff (n : Nat) (cut : Cut) :
    cut.validBool n = true ↔ cut.Valid n := by
  cases cut <;> rfl

/-- Executable validity test for a complete witness stream. -/
def cutsValidBool (n : Nat) (cuts : List Cut) : Bool :=
  cuts.all (Cut.validBool n)

theorem valid_of_cutsValidBool {n : Nat} {cuts : List Cut}
    (h : cutsValidBool n cuts = true) :
    ∀ cut ∈ cuts, cut.Valid n := by
  intro cut hcut
  have hall : ∀ c ∈ cuts, c.validBool n = true := by
    simpa [cutsValidBool] using h
  exact (Cut.validBool_eq_true_iff n cut).mp (hall cut hcut)

theorem valid_of_cutsValidBool_drop_take {n : Nat} {cuts : List Cut}
    (h : cutsValidBool n cuts = true) (start length : Nat) :
    ∀ cut ∈ (cuts.drop start).take length, cut.Valid n := by
  intro cut hcut
  exact valid_of_cutsValidBool h cut
    (List.mem_of_mem_drop (List.mem_of_mem_take hcut))

/-- Literal closure clauses for one possible triangle. -/
def triangleClosureBlock (n : Nat)
    (entry : (Fin n × Fin n × Fin n) × Nat) : Sat.Fmla :=
  let (t, triangleIndex) := entry
  let triangleVar := triangleVariable n triangleIndex
  let edgeVars := (triangleEdges t).map edgeVariable
  edgeVars.map (fun edgeVar => [.neg triangleVar, .pos edgeVar]) ++
    [edgeVars.map Sat.Literal.neg ++ [.pos triangleVar]]

/-- Literal closure clauses for every possible triangle. -/
def triangleClosureClauses (n : Nat) : Sat.Fmla :=
  (orderedTriangles n).zipIdx.flatMap (triangleClosureBlock n)

/-- Every selected edge must lie in a selected triangle. -/
def edgeSupportClause (n : Nat) (entry : (Fin n × Fin n) × Nat) : Sat.Clause :=
  let (e, edgeIndex) := entry
  .neg edgeIndex ::
    ((orderedTriangles n).zipIdx.filterMap fun (t, triangleIndex) =>
      if e ∈ triangleEdges t then
        some (.pos (triangleVariable n triangleIndex))
      else none)

/-- Every selected edge must lie in a selected triangle. -/
def edgeSupportClauses (n : Nat) : Sat.Fmla :=
  (orderedEdges n).zipIdx.map (edgeSupportClause n)

/-- Every labelled vertex must lie in a selected triangle. -/
def vertexSupportClause (n : Nat) (vertex : Fin n) : Sat.Clause :=
    (orderedTriangles n).zipIdx.filterMap fun (t, triangleIndex) =>
      if vertex == t.1 || vertex == t.2.1 || vertex == t.2.2 then
        some (.pos (triangleVariable n triangleIndex))
      else none

/-- Every labelled vertex must lie in a selected triangle. -/
def vertexSupportClauses (n : Nat) : Sat.Fmla :=
  (List.finRange n).map (vertexSupportClause n)

/-- Unit clauses selecting the marked four-packing. -/
def markedPackingClauses (n : Nat) (triangleIndices : List Nat) : Sat.Fmla :=
  triangleIndices.map fun triangleIndex => [.pos (triangleVariable n triangleIndex)]

/-- The exact non-learned prefix of an ambient rank-four formula. -/
def baseFormula (n : Nat) (markedPacking : List Nat) : Sat.Fmla :=
  triangleClosureClauses n ++ edgeSupportClauses n ++
    vertexSupportClauses n ++ markedPackingClauses n markedPacking

/-- Propositional conditions expressed by the non-learned formula prefix. -/
structure BaseConditions (n : Nat) (v : Sat.Valuation)
    (markedPacking : List Nat) : Prop where
  triangleClosure : ∀ {i} {t : Fin n × Fin n × Fin n},
    (orderedTriangles n)[i]? = some t →
      (v (triangleVariable n i) ↔
        ∀ e ∈ triangleEdges t, v (edgeVariable e))
  edgeSupported : ∀ {i} {e : Fin n × Fin n},
    (orderedEdges n)[i]? = some e → v i →
      ∃ j t, (orderedTriangles n)[j]? = some t ∧
        e ∈ triangleEdges t ∧ v (triangleVariable n j)
  vertexSupported : ∀ (vertex : Fin n),
    ∃ j t, (orderedTriangles n)[j]? = some t ∧
      (vertex == t.1 || vertex == t.2.1 || vertex == t.2.2) ∧
      v (triangleVariable n j)
  marked : ∀ (i : Nat), List.Mem i markedPacking → v (triangleVariable n i)

private theorem satisfies_triangleClosureBlock {n : Nat} {v : Sat.Valuation}
    {i : Nat} {t : Fin n × Fin n × Fin n}
    (h : BaseConditions n v [])
    (hget : (orderedTriangles n)[i]? = some t) :
    v.satisfies_fmla (triangleClosureBlock n (t, i)) := by
  classical
  refine ⟨?_⟩
  intro clause hclause
  rw [satisfies_iff_exists_literalTrue]
  simp only [triangleClosureBlock] at hclause
  rcases List.mem_append.mp hclause with hbinary | hlast
  · obtain ⟨edgeVar, hedgeVar, rfl⟩ := List.mem_map.mp hbinary
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hedgeVar
    by_cases htriangle : v (triangleVariable n i)
    · refine ⟨.pos (edgeVariable e), .tail _ (.head _), ?_⟩
      exact h.triangleClosure hget |>.mp htriangle e he
    · exact ⟨.neg (triangleVariable n i), .head _, htriangle⟩
  · have hEq : clause =
        (triangleEdges t).map (fun e => Sat.Literal.neg (edgeVariable e)) ++
          [.pos (triangleVariable n i)] := by
      change List.Mem clause
        [(triangleEdges t).map (fun e => Sat.Literal.neg (edgeVariable e)) ++
          [.pos (triangleVariable n i)]] at hlast
      exact List.mem_singleton.mp hlast
    rw [hEq]
    by_cases hall : ∀ e ∈ triangleEdges t, v (edgeVariable e)
    · refine ⟨.pos (triangleVariable n i), ?_, h.triangleClosure hget |>.mpr hall⟩
      exact List.mem_append.mpr (Or.inr (.head _))
    · push_neg at hall
      obtain ⟨e, he, hfalse⟩ := hall
      refine ⟨.neg (edgeVariable e), ?_, hfalse⟩
      apply List.mem_append.mpr
      left
      exact List.mem_map.mpr ⟨e, he, rfl⟩

private theorem satisfies_edgeSupportClause {n : Nat} {v : Sat.Valuation}
    {i : Nat} {e : Fin n × Fin n}
    (h : BaseConditions n v [])
    (hget : (orderedEdges n)[i]? = some e) :
    v.satisfies (edgeSupportClause n (e, i)) := by
  classical
  rw [satisfies_iff_exists_literalTrue]
  by_cases hedge : v i
  · obtain ⟨j, t, htget, het, httrue⟩ := h.edgeSupported hget hedge
    refine ⟨.pos (triangleVariable n j), ?_, httrue⟩
    apply List.Mem.tail
    simp only [edgeSupportClause]
    apply List.mem_filterMap.mpr
    have hjlt : j < (orderedTriangles n).length := by
      exact List.getElem?_eq_some_iff.mp htget |>.1
    refine ⟨(t, j), ?_, ?_⟩
    · exact List.mem_iff_getElem.mpr ⟨j, by simpa using hjlt, by
        simpa using (List.getElem?_eq_some_iff.mp htget).2⟩
    · simp [het]
  · exact ⟨.neg i, .head _, hedge⟩

private theorem satisfies_vertexSupportClause {n : Nat} {v : Sat.Valuation}
    {vertex : Fin n} (h : BaseConditions n v []) :
    v.satisfies (vertexSupportClause n vertex) := by
  rw [satisfies_iff_exists_literalTrue]
  obtain ⟨j, t, htget, hcontains, httrue⟩ := h.vertexSupported vertex
  refine ⟨.pos (triangleVariable n j), ?_, httrue⟩
  simp only [vertexSupportClause]
  apply List.mem_filterMap.mpr
  have hjlt : j < (orderedTriangles n).length :=
    List.getElem?_eq_some_iff.mp htget |>.1
  refine ⟨(t, j), ?_, ?_⟩
  · exact List.mem_iff_getElem.mpr ⟨j, by simpa using hjlt, by
      simpa using (List.getElem?_eq_some_iff.mp htget).2⟩
  · simp [hcontains]

/-- The abstract base conditions satisfy the exact non-learned formula. -/
theorem satisfies_baseFormula {n : Nat} {v : Sat.Valuation}
    {markedPacking : List Nat} (h : BaseConditions n v markedPacking) :
    v.satisfies_fmla (baseFormula n markedPacking) := by
  classical
  have hempty : BaseConditions n v [] :=
    { triangleClosure := h.triangleClosure
      edgeSupported := h.edgeSupported
      vertexSupported := h.vertexSupported
      marked := fun _ hmem => nomatch hmem }
  refine ⟨?_⟩
  intro clause hclause
  simp only [baseFormula, List.mem_append] at hclause
  rcases hclause with ((htriangle | hedge) | hvertex) | hmarked
  · obtain ⟨entry, hentry, hclause⟩ := List.mem_flatMap.mp htriangle
    obtain ⟨i, hi, rfl⟩ := List.exists_mem_zipIdx'.mp ⟨entry, hentry, rfl⟩
    exact (satisfies_triangleClosureBlock hempty (List.getElem?_eq_getElem hi)).prop
      clause hclause
  · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hedge
    obtain ⟨i, hi, rfl⟩ := List.exists_mem_zipIdx'.mp ⟨entry, hentry, rfl⟩
    exact satisfies_edgeSupportClause hempty (List.getElem?_eq_getElem hi)
  · obtain ⟨vertex, hvertexMem, rfl⟩ := List.mem_map.mp hvertex
    exact satisfies_vertexSupportClause hempty
  · obtain ⟨i, hi, hEq⟩ := List.mem_map.mp hmarked
    rw [← hEq]
    rw [satisfies_iff_exists_literalTrue]
    exact ⟨.pos (triangleVariable n i), .head _, h.marked i hi⟩

/-- A supported labelled graph with no isolated labelled vertices satisfies
the exact base conditions. -/
theorem graphValuation_baseConditions {n : Nat} (G : SimpleGraph (Fin n))
    (markedPacking : List Nat)
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin n, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles n)[i]? = some t ∧
        triangleFinset t ∈ G.triangles) :
    BaseConditions n (graphValuation G) markedPacking := by
  classical
  constructor
  · intro i t hget
    have htmem : t ∈ orderedTriangles n := by
      have hi := List.getElem?_eq_some_iff.mp hget
      exact List.mem_iff_getElem.mpr ⟨i, hi.1, hi.2⟩
    constructor
    · intro httrue e he
      have hadj := (graphValuation_triangle_at G hget).mp httrue
      have heOrdered := triangleEdges_mem_orderedEdges htmem e he
      rw [graphValuation_edgeVariable G heOrdered]
      simp only [triangleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hadj.1
      · exact hadj.2.1
      · exact hadj.2.2
    · intro hedges
      apply (graphValuation_triangle_at G hget).mpr
      refine ⟨?_, ?_, ?_⟩
      · let e : Fin n × Fin n := (t.1, t.2.1)
        apply (graphValuation_edgeVariable G
          (triangleEdges_mem_orderedEdges htmem e (by simp [e, triangleEdges]))).mp
        exact hedges e (by simp [e, triangleEdges])
      · let e : Fin n × Fin n := (t.1, t.2.2)
        apply (graphValuation_edgeVariable G
          (triangleEdges_mem_orderedEdges htmem e (by simp [e, triangleEdges]))).mp
        exact hedges e (by simp [e, triangleEdges])
      · let e : Fin n × Fin n := (t.2.1, t.2.2)
        apply (graphValuation_edgeVariable G
          (triangleEdges_mem_orderedEdges htmem e (by simp [e, triangleEdges]))).mp
        exact hedges e (by simp [e, triangleEdges])
  · intro i e hget hetrue
    have hi := List.getElem?_eq_some_iff.mp hget
    have heOrdered : e ∈ orderedEdges n :=
      List.mem_iff_getElem.mpr ⟨i, hi.1, hi.2⟩
    have heAdj : G.Adj e.1 e.2 :=
      (graphValuation_edge_at G hget).mp hetrue
    have heSupport : G.triangleSupport.Adj e.1 e.2 := by
      rw [hSupport]
      exact heAdj
    obtain ⟨s, hs, heFirst, heSecond, _⟩ := heSupport
    have hsClique : G.IsNClique 3 s := by
      simpa [SimpleGraph.triangles] using hs
    obtain ⟨t, htOrdered, htEq⟩ :=
      exists_orderedTriangle_of_card_eq_three s hsClique.card_eq
    let j := (orderedTriangles n).idxOf t
    have htget : (orderedTriangles n)[j]? = some t :=
      List.getElem?_idxOf htOrdered
    have het : e ∈ triangleEdges t :=
      (mem_triangleEdges_iff_edgeFinset_subset heOrdered htOrdered).mpr (by
        intro x hx
        simp [edgeFinset] at hx
        rw [htEq]
        rcases hx with rfl | rfl
        · exact heFirst
        · exact heSecond)
    refine ⟨j, t, htget, het, ?_⟩
    apply (graphValuation_triangle_at G htget).mpr
    exact (triangleFinset_mem_triangles_iff G htOrdered).mp (by
      rw [htEq]
      exact hs)
  · intro vertex
    obtain ⟨s, hs, hvs⟩ :=
      G.mem_triangleSupportVertices_iff.mp (hVertices vertex)
    have hsClique : G.IsNClique 3 s := by
      simpa [SimpleGraph.triangles] using hs
    obtain ⟨t, htOrdered, htEq⟩ :=
      exists_orderedTriangle_of_card_eq_three s hsClique.card_eq
    let j := (orderedTriangles n).idxOf t
    have htget : (orderedTriangles n)[j]? = some t :=
      List.getElem?_idxOf htOrdered
    have hvt : vertex ∈ triangleFinset t := by
      rw [htEq]
      exact hvs
    refine ⟨j, t, htget, ?_, ?_⟩
    · simp [triangleFinset] at hvt
      rcases hvt with hvt | hvt | hvt
      · simp [hvt]
      · simp [hvt]
      · simp [hvt]
    · apply (graphValuation_triangle_at G htget).mpr
      exact (triangleFinset_mem_triangles_iff G htOrdered).mp (by
        rw [htEq]
        exact hs)
  · intro i hi
    obtain ⟨t, htget, htG⟩ := hMarked i hi
    apply (graphValuation_triangle_at G htget).mpr
    have htmem : t ∈ orderedTriangles n := by
      have hindex := List.getElem?_eq_some_iff.mp htget
      exact List.mem_iff_getElem.mpr ⟨i, hindex.1, hindex.2⟩
    exact (triangleFinset_mem_triangles_iff G htmem).mp htG

/-- The negative clause excluding five simultaneously present triangles. -/
def packingClause (n : Nat) (indices : List Nat) : Sat.Clause :=
  indices.map fun i => .neg (triangleVariable n i)

/-- Whether an ordered triangle avoids every decoded cover edge. -/
def avoidsCover {n : Nat} (cover : List (Fin n × Fin n))
    (t : Fin n × Fin n × Fin n) : Bool :=
  (triangleEdges t).all fun e => !cover.contains e

/-- The positive clause requiring a triangle missed by a proposed cover. -/
def coverClause (n : Nat) (indices : List Nat) : Sat.Clause :=
  let cover := decodeEdges n indices
  (orderedTriangles n).zipIdx.filterMap fun (t, i) =>
    if avoidsCover cover t then some (.pos (triangleVariable n i)) else none

/-- Reconstruct the exact learned clause represented by a witness. -/
def Cut.clause (n : Nat) : Cut → Sat.Clause
  | .packing indices => packingClause n indices
  | .cover indices => coverClause n indices

/-- The learned-clause suffix represented by a witness stream. -/
def cutFormula (n : Nat) (cuts : List Cut) : Sat.Fmla :=
  cuts.map (Cut.clause n)

/-- Abstract semantic conditions sufficient to satisfy every learned cut.
They deliberately mention only the decoded witnesses and the propositional
valuation; the graph-theoretic consequences are proved separately. -/
structure CutConditions (n : Nat) (v : Sat.Valuation) : Prop where
  noFive : ∀ indices, PackingValid n indices →
    ¬∀ i ∈ indices, v (triangleVariable n i)
  missesSmallCover : ∀ indices, CoverValid n indices →
    ∃ t ∈ (orderedTriangles n).zipIdx,
      avoidsCover (decodeEdges n indices) t.1 ∧
      v (triangleVariable n t.2)

theorem avoidsCover_eq_true_iff {n : Nat}
    (cover : List (Fin n × Fin n)) (t : Fin n × Fin n × Fin n) :
    avoidsCover cover t = true ↔
      ∀ e ∈ triangleEdges t, e ∉ cover := by
  simp [avoidsCover]

/-- If the graph has transversal number greater than eight, every valid
eight-edge cover witness misses an actual graph triangle. -/
theorem graphValuation_missesSmallCover {n : Nat} (G : SimpleGraph (Fin n))
    (hτ : 8 < G.triangleTransversalNumber) :
    ∀ indices, CoverValid n indices →
      ∃ t ∈ (orderedTriangles n).zipIdx,
        avoidsCover (decodeEdges n indices) t.1 ∧
        graphValuation G (triangleVariable n t.2) := by
  classical
  intro indices hvalid
  let decoded := decodeEdges n indices
  have hdecoded : decoded.length ≤ 8 := by
    exact of_decide_eq_true hvalid
  let raw : Finset (Finset (Fin n)) :=
    (decoded.map edgeFinset).toFinset
  let C : Finset (Finset (Fin n)) := raw ∩ G.edges
  have hCcard : C.card ≤ 8 := by
    calc
      C.card ≤ raw.card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ (decoded.map edgeFinset).length := by
        simpa [raw] using List.toFinset_card_le (decoded.map edgeFinset)
      _ = decoded.length := by simp
      _ ≤ 8 := hdecoded
  have hnotTransversal : ¬G.IsTriangleTransversal C := by
    intro hC
    have hbound := G.triangleTransversalNumber_le_card hC
    omega
  have hmiss : ∃ s ∈ G.triangles, ∀ e ∈ C, ¬e ⊆ s := by
    by_contra hnone
    apply hnotTransversal
    constructor
    · exact Finset.inter_subset_right
    · intro s hs
      by_contra hnoedge
      push Not at hnoedge
      apply hnone
      exact ⟨s, hs, hnoedge⟩
  obtain ⟨s, hs, hmisses⟩ := hmiss
  have hscard : s.card = 3 := by
    have hsClique : G.IsNClique 3 s := by
      simpa [SimpleGraph.triangles] using hs
    exact hsClique.card_eq
  obtain ⟨t, htOrdered, htFinset⟩ :=
    exists_orderedTriangle_of_card_eq_three s hscard
  have htG : triangleFinset t ∈ G.triangles := by
    rw [htFinset]
    exact hs
  have hav : avoidsCover decoded t = true := by
    rw [avoidsCover_eq_true_iff]
    intro e heTriangle heDecoded
    have heOrdered : e ∈ orderedEdges n :=
      decodeEdge_mem_orderedEdges heDecoded
    have heRaw : edgeFinset e ∈ raw := by
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, heDecoded, rfl⟩)
    have heSubset : edgeFinset e ⊆ triangleFinset t :=
      (mem_triangleEdges_iff_edgeFinset_subset heOrdered htOrdered).mp heTriangle
    have heG : edgeFinset e ∈ G.edges :=
      G.mem_edges_of_subset_triangle htG heSubset
        (edgeFinset_card_of_mem_orderedEdges heOrdered)
    have heC : edgeFinset e ∈ C := Finset.mem_inter.mpr ⟨heRaw, heG⟩
    exact hmisses (edgeFinset e) heC (by simpa [htFinset] using heSubset)
  rw [List.exists_mem_zipIdx']
  let i := (orderedTriangles n).idxOf t
  have hi : i < (orderedTriangles n).length :=
    List.idxOf_lt_length_of_mem htOrdered
  refine ⟨i, hi, ?_⟩
  have hget : (orderedTriangles n)[i] = t :=
    List.getElem_idxOf hi
  have htrue : graphValuation G (triangleVariable n i) := by
    apply (graphValuation_triangle_at G ?_).mpr
    · exact (triangleFinset_mem_triangles_iff G htOrdered).mp htG
    · exact List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  simpa [hget, decoded] using And.intro hav htrue

/-- The graph-theoretic rank and transversal bounds imply the abstract
conditions used to validate every semantic learned clause. -/
theorem graphValuation_cutConditions {n : Nat} (G : SimpleGraph (Fin n))
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) :
    CutConditions n (graphValuation G) :=
  ⟨graphValuation_noFive G hν, graphValuation_missesSmallCover G hτ⟩

private theorem mem_map_triangleVariable {n : Nat} {indices : List Nat} {i : Nat}
    (hi : i ∈ indices) :
    List.Mem (Sat.Literal.neg (triangleVariable n i))
      (packingClause n indices) := by
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- A valid packing witness is satisfied under the no-five condition. -/
theorem satisfies_packingClause {n : Nat} {v : Sat.Valuation}
    (h : CutConditions n v) (indices : List Nat)
    (hvalid : PackingValid n indices) :
    v.satisfies (packingClause n indices) := by
  classical
  rw [satisfies_iff_exists_literalTrue]
  by_contra hnone
  apply h.noFive indices hvalid
  intro i hi
  apply Classical.byContradiction
  intro hfalse
  apply hnone
  exact ⟨.neg (triangleVariable n i), mem_map_triangleVariable (n := n) hi,
    by simpa [literalTrue] using hfalse⟩

/-- A valid cover witness is satisfied under the small-cover escape
condition. -/
theorem satisfies_coverClause {n : Nat} {v : Sat.Valuation}
    (h : CutConditions n v) (indices : List Nat)
    (hvalid : CoverValid n indices) :
    v.satisfies (coverClause n indices) := by
  rw [satisfies_iff_exists_literalTrue]
  obtain ⟨⟨t, i⟩, hmem, hav, htrue⟩ := h.missesSmallCover indices hvalid
  refine ⟨.pos (triangleVariable n i), ?_, by simpa [literalTrue] using htrue⟩
  simp only [coverClause]
  apply List.mem_filterMap.mpr
  refine ⟨(t, i), hmem, ?_⟩
  simp [hav]

/-- Every valid learned clause is satisfied by a valuation obeying the two
mathematical cut conditions. -/
theorem satisfies_cut {n : Nat} {v : Sat.Valuation}
    (h : CutConditions n v) (cut : Cut) (hvalid : cut.Valid n) :
    v.satisfies (cut.clause n) := by
  cases cut with
  | packing indices => exact satisfies_packingClause h indices hvalid
  | cover indices => exact satisfies_coverClause h indices hvalid

/-- A stream of valid semantic witnesses yields satisfaction of the entire
learned-clause suffix. -/
theorem satisfies_cutFormula {n : Nat} {v : Sat.Valuation}
    (h : CutConditions n v) (cuts : List Cut)
    (hvalid : ∀ cut ∈ cuts, cut.Valid n) :
    v.satisfies_fmla (cutFormula n cuts) := by
  refine ⟨?_⟩
  intro clause hclause
  obtain ⟨cut, hcut, rfl⟩ := List.mem_map.mp hclause
  exact satisfies_cut h cut (hvalid cut hcut)

theorem satisfies_fmla_append {v : Sat.Valuation} {f₁ f₂ : Sat.Fmla}
    (h₁ : v.satisfies_fmla f₁) (h₂ : v.satisfies_fmla f₂) :
    v.satisfies_fmla (f₁ ++ f₂) := by
  refine ⟨?_⟩
  intro clause hclause
  rcases List.mem_append.mp hclause with hleft | hright
  · exact h₁.prop clause hleft
  · exact h₂.prop clause hright

theorem satisfies_fmla_drop_take {v : Sat.Valuation} {f : Sat.Fmla}
    (h : v.satisfies_fmla f) (start length : Nat) :
    v.satisfies_fmla ((f.drop start).take length) := by
  refine ⟨?_⟩
  intro clause hclause
  exact h.prop clause (List.mem_of_mem_drop (List.mem_of_mem_take hclause))

/-- Turn one exact finite formula identity and its checked LRAT refutation
into the corresponding graph-theoretic impossibility statement. -/
theorem false_of_semantic_refutation {n : Nat}
    (G : SimpleGraph (Fin n)) (formula : Sat.Fmla)
    (markedPacking : List Nat) (cuts : List Cut)
    (hFormula : formula = baseFormula n markedPacking ++ cutFormula n cuts)
    (hCuts : cutsValidBool n cuts = true)
    (hRefutation : formula.proof [])
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin n, v ∈ G.triangleSupportVertices)
    (hMarked : ∀ i, List.Mem i markedPacking →
      ∃ t, (orderedTriangles n)[i]? = some t ∧
        triangleFinset t ∈ G.triangles)
    (hν : G.trianglePackingNumber ≤ 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  let v := graphValuation G
  have hBaseConditions : BaseConditions n v markedPacking :=
    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked
  have hCutConditions : CutConditions n v :=
    graphValuation_cutConditions G hν hτ
  have hBase : v.satisfies_fmla (baseFormula n markedPacking) :=
    satisfies_baseFormula hBaseConditions
  have hCut : v.satisfies_fmla (cutFormula n cuts) :=
    satisfies_cutFormula hCutConditions cuts (valid_of_cutsValidBool hCuts)
  have hAll : v.satisfies_fmla formula := by
    rw [hFormula]
    exact satisfies_fmla_append hBase hCut
  exact hRefutation v hAll

end TuzaRankFour.SemanticEncoding
