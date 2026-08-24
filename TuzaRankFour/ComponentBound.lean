import TuzaRankFour.Discharge
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The component size bound

The clean way to count the vertex support of a connected family of triangles
is to use its bipartite incidence graph.  If the family has `k` triangles and
its support has `m` vertices, that incidence graph has `k + m` vertices and
`3k` edges.  Connectedness therefore gives `k + m ≤ 3k + 1`, hence
`m ≤ 2k + 1`.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bipartite incidence graph between a finite triangle family and the
vertices in its support. -/
def familyIncidenceGraph (P : Finset (Finset V)) :
    SimpleGraph
      (Sum {t : Finset V // t ∈ P}
        {v : V // v ∈ triangleFamilyVertexSupport P}) where
  Adj x y :=
    match x, y with
    | Sum.inl t, Sum.inr v => v.1 ∈ t.1
    | Sum.inr v, Sum.inl t => v.1 ∈ t.1
    | _, _ => False
  symm.symm := by
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless.irrefl := by
    intro x
    cases x <;> simp

noncomputable instance familyIncidenceGraphDecidableAdj
    (P : Finset (Finset V)) :
    DecidableRel (familyIncidenceGraph P).Adj :=
  Classical.decRel _

omit [Fintype V] in
@[simp]
theorem familyIncidenceGraph_adj_inl_inr_iff
    {P : Finset (Finset V)}
    {t : {q : Finset V // q ∈ P}}
    {v : {x : V // x ∈ triangleFamilyVertexSupport P}} :
    (familyIncidenceGraph P).Adj (Sum.inl t) (Sum.inr v) ↔
      v.1 ∈ t.1 :=
  Iff.rfl

omit [Fintype V] in
@[simp]
theorem familyIncidenceGraph_adj_inr_inl_iff
    {P : Finset (Finset V)}
    {t : {q : Finset V // q ∈ P}}
    {v : {x : V // x ∈ triangleFamilyVertexSupport P}} :
    (familyIncidenceGraph P).Adj (Sum.inr v) (Sum.inl t) ↔
      v.1 ∈ t.1 :=
  Iff.rfl

omit [Fintype V] in
@[simp]
theorem not_familyIncidenceGraph_adj_inl_inl
    {P : Finset (Finset V)}
    {s t : {q : Finset V // q ∈ P}} :
    ¬(familyIncidenceGraph P).Adj (Sum.inl s) (Sum.inl t) := by
  simp [familyIncidenceGraph]

omit [Fintype V] in
@[simp]
theorem not_familyIncidenceGraph_adj_inr_inr
    {P : Finset (Finset V)}
    {v w : {x : V // x ∈ triangleFamilyVertexSupport P}} :
    ¬(familyIncidenceGraph P).Adj (Sum.inr v) (Sum.inr w) := by
  simp [familyIncidenceGraph]

/-- The triangle side of the incidence bipartition. -/
noncomputable def familyIncidenceLeft (P : Finset (Finset V)) :
    Finset
      (Sum {t : Finset V // t ∈ P}
        {v : V // v ∈ triangleFamilyVertexSupport P}) :=
  Finset.univ.image Sum.inl

/-- The support-vertex side of the incidence bipartition. -/
noncomputable def familyIncidenceRight (P : Finset (Finset V)) :
    Finset
      (Sum {t : Finset V // t ∈ P}
        {v : V // v ∈ triangleFamilyVertexSupport P}) :=
  Finset.univ.image Sum.inr

@[simp]
theorem mem_familyIncidenceLeft_iff
    {P : Finset (Finset V)}
    {x : Sum {t : Finset V // t ∈ P}
      {v : V // v ∈ triangleFamilyVertexSupport P}} :
    x ∈ familyIncidenceLeft P ↔ ∃ t, Sum.inl t = x := by
  classical
  simp [familyIncidenceLeft]

@[simp]
theorem mem_familyIncidenceRight_iff
    {P : Finset (Finset V)}
    {x : Sum {t : Finset V // t ∈ P}
      {v : V // v ∈ triangleFamilyVertexSupport P}} :
    x ∈ familyIncidenceRight P ↔ ∃ v, Sum.inr v = x := by
  classical
  simp [familyIncidenceRight]

theorem familyIncidenceGraph_isBipartiteWith
    (P : Finset (Finset V)) :
    (familyIncidenceGraph P).IsBipartiteWith
      (familyIncidenceLeft P : Set _)
      (familyIncidenceRight P : Set _) := by
  classical
  constructor
  · rw [Set.disjoint_left]
    intro x hxLeft hxRight
    obtain ⟨t, rfl⟩ := mem_familyIncidenceLeft_iff.mp hxLeft
    simp at hxRight
  · intro x y hxy
    cases x with
    | inl t =>
        cases y with
        | inl s => simp at hxy
        | inr v =>
            exact Or.inl ⟨by simp, by simp⟩
    | inr v =>
        cases y with
        | inl t =>
            exact Or.inr ⟨by simp, by simp⟩
        | inr w => simp at hxy

/-- A triangle vertex in the incidence graph has degree equal to the number
of vertices of that triangle. -/
theorem familyIncidenceGraph_degree_inl
    {P : Finset (Finset V)} (t : {q : Finset V // q ∈ P}) :
    (familyIncidenceGraph P).degree (Sum.inl t) = t.1.card := by
  classical
  rw [← (familyIncidenceGraph P).card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij
      (fun v hv ↦ Sum.inr
        ⟨v, Finset.mem_biUnion.mpr ⟨t.1, t.2, hv⟩⟩)
  · intro v hv
    rw [(familyIncidenceGraph P).mem_neighborFinset]
    exact hv
  · intro v hv w hw heq
    simpa using heq
  · intro x hx
    rw [(familyIncidenceGraph P).mem_neighborFinset] at hx
    cases x with
    | inl s => simp at hx
    | inr v =>
        refine ⟨v.1, hx, ?_⟩
        apply congrArg Sum.inr
        apply Subtype.ext
        rfl

/-- The incidence edge count is the sum of the family-member cardinalities. -/
theorem familyIncidenceGraph_card_edgeFinset
    (P : Finset (Finset V)) :
    (familyIncidenceGraph P).edgeFinset.card =
      ∑ t : {q : Finset V // q ∈ P}, t.1.card := by
  classical
  have hdegree :
      ∑ x ∈ familyIncidenceLeft P, (familyIncidenceGraph P).degree x =
        (familyIncidenceGraph P).edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
      (familyIncidenceGraph_isBipartiteWith P)
  calc
    (familyIncidenceGraph P).edgeFinset.card =
        ∑ x ∈ familyIncidenceLeft P, (familyIncidenceGraph P).degree x :=
      hdegree.symm
    _ = ∑ t : {q : Finset V // q ∈ P}, t.1.card := by
      rw [familyIncidenceLeft,
        Finset.sum_image Sum.inl_injective.injOn]
      simp [familyIncidenceGraph_degree_inl]

/-- If every member of the family has three vertices, its incidence graph has
exactly three incidence edges per family member. -/
theorem familyIncidenceGraph_card_edgeFinset_of_card_three
    {P : Finset (Finset V)}
    (hcard : ∀ t ∈ P, t.card = 3) :
    (familyIncidenceGraph P).edgeFinset.card = 3 * P.card := by
  rw [familyIncidenceGraph_card_edgeFinset]
  simp [hcard, mul_comm]

/-- A path through the intersection graph lifts to a path through the
incidence graph, replacing each shared-vertex adjacency by two incidence
edges. -/
theorem familyIncidenceGraph_reachable_inl_of_reachable
    {P : Finset (Finset V)}
    {s t : {q : Finset V // q ∈ P}}
    (hst : (packingIntersectionGraph P).Reachable s t) :
    (familyIncidenceGraph P).Reachable (Sum.inl s) (Sum.inl t) := by
  classical
  rw [reachable_iff_reflTransGen] at hst ⊢
  apply hst.lift' (fun q ↦ Sum.inl q)
  intro a b hab
  obtain ⟨_, hinter⟩ := packingIntersectionGraph_adj_iff.mp hab
  obtain ⟨v, hvinter⟩ := hinter
  have ⟨hva, hvb⟩ := Finset.mem_inter.mp hvinter
  let vSupport : {x : V // x ∈ triangleFamilyVertexSupport P} :=
    ⟨v, Finset.mem_biUnion.mpr ⟨a.1, a.2, hva⟩⟩
  have haIncidence :
      (familyIncidenceGraph P).Adj (Sum.inl a) (Sum.inr vSupport) :=
    familyIncidenceGraph_adj_inl_inr_iff.mpr hva
  have hbIncidence :
      (familyIncidenceGraph P).Adj (Sum.inr vSupport) (Sum.inl b) :=
    familyIncidenceGraph_adj_inr_inl_iff.mpr hvb
  exact (Relation.ReflTransGen.single haIncidence).trans
    (Relation.ReflTransGen.single hbIncidence)

/-- Connectedness of the family-intersection graph implies connectedness of
the corresponding incidence graph. -/
theorem familyIncidenceGraph_connected
    {P : Finset (Finset V)}
    (hConnected : (packingIntersectionGraph P).Connected) :
    (familyIncidenceGraph P).Connected := by
  classical
  rw [connected_iff_exists_forall_reachable]
  let root : {q : Finset V // q ∈ P} := Classical.choice hConnected.nonempty
  refine ⟨Sum.inl root, ?_⟩
  intro x
  cases x with
  | inl t =>
      exact familyIncidenceGraph_reachable_inl_of_reachable
        (hConnected root t)
  | inr v =>
      obtain ⟨t, htP, hvt⟩ := Finset.mem_biUnion.mp v.2
      let packedTriangle : {q : Finset V // q ∈ P} := ⟨t, htP⟩
      exact (familyIncidenceGraph_reachable_inl_of_reachable
        (hConnected root packedTriangle)).trans
          (SimpleGraph.Adj.reachable
            (familyIncidenceGraph_adj_inl_inr_iff.mpr hvt))

/-- A connected family of three-element sets has support size at most twice
the family size plus one.  This is the incidence-graph count
`k + m ≤ 3k + 1`. -/
theorem card_triangleFamilyVertexSupport_le_two_mul_add_one
    {P : Finset (Finset V)}
    (hConnected : (packingIntersectionGraph P).Connected)
    (hcard : ∀ t ∈ P, t.card = 3) :
    (triangleFamilyVertexSupport P).card ≤ 2 * P.card + 1 := by
  classical
  have hConnectedIncidence := familyIncidenceGraph_connected hConnected
  have hVertexEdge :=
    hConnectedIncidence.card_vert_le_card_edgeSet_add_one
  have hEdgeCard :
      Nat.card (familyIncidenceGraph P).edgeSet =
        (familyIncidenceGraph P).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  rw [hEdgeCard] at hVertexEdge
  have hCount :
      P.card + (triangleFamilyVertexSupport P).card ≤
        (familyIncidenceGraph P).edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card] using hVertexEdge
  rw [familyIncidenceGraph_card_edgeFinset_of_card_three hcard] at hCount
  omega

/-- Forget the component-membership proof and regard a component vertex as a
member of the corresponding finite triangle family. -/
noncomputable def packingComponentGraphHom
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    C.toSimpleGraph →g
      packingIntersectionGraph (packingComponentTriangles S C) where
  toFun q :=
    ⟨q.1.1, mem_packingComponentTriangles_iff.mpr ⟨q, rfl⟩⟩
  map_rel' := by
    intro q r hqr
    have hOriginal : (packingIntersectionGraph S).Adj q.1 r.1 :=
      (C.toSimpleGraph_adj q.2 r.2).mp hqr
    refine packingIntersectionGraph_adj_iff.mpr ⟨?_, hOriginal.2⟩
    intro hMapped
    apply hOriginal.1
    apply Subtype.ext
    exact congrArg
      (fun z : {t : Finset V // t ∈ packingComponentTriangles S C} ↦ z.1)
      hMapped

theorem packingComponentGraphHom_surjective
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    Function.Surjective (packingComponentGraphHom S C) := by
  classical
  intro t
  obtain ⟨q, hqt⟩ := mem_packingComponentTriangles_iff.mp t.2
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact hqt

/-- The finite family belonging to one packing-intersection component is
itself connected under nonempty intersection. -/
theorem packingComponentTriangles_connected
    (S : Finset (Finset V))
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    (packingIntersectionGraph
      (packingComponentTriangles S C)).Connected :=
  C.connected_toSimpleGraph.map (packingComponentGraphHom S C)
    (packingComponentGraphHom_surjective S C)

/-- A component containing `k` packed triangles covers at most `2k+1`
vertices. -/
theorem card_packingComponentVertexSupport_le
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (hS : G.IsTrianglePacking S)
    (C : (packingIntersectionGraph S).ConnectedComponent) :
    (packingComponentVertexSupport S C).card ≤
      2 * (packingComponentTriangles S C).card + 1 := by
  apply card_triangleFamilyVertexSupport_le_two_mul_add_one
    (packingComponentTriangles_connected S C)
  intro t htC
  exact G.card_eq_three_of_mem_triangles
    (hS.1 (packingComponentTriangles_subset C htC))

end SimpleGraph
