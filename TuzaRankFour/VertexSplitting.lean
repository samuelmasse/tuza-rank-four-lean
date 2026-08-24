import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic
import TuzaRankFour.Reduction

/-!
# Canonical vertex splitting

At a vertex `v`, two incident edges belong to a common triangle exactly when
their other endpoints are adjacent in the graph induced on the neighbors of
`v`.  Thus the connected components of this link graph are the canonical
copies into which `v` is split.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The link graph at `v`: the original graph induced on the neighbors of
`v`. -/
def triangleLink (G : SimpleGraph V) (v : V) :
    SimpleGraph (G.neighborSet v) :=
  G.induce (G.neighborSet v)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem triangleLink_adj_iff (G : SimpleGraph V) (v : V)
    {x y : G.neighborSet v} :
    (G.triangleLink v).Adj x y ↔ G.Adj x y :=
  Iff.rfl

/-- A graph is split-normal when every vertex link is preconnected.  Empty
and singleton links satisfy this condition vacuously. -/
def IsSplitNormal (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.triangleLink v).Preconnected

/-- A vertex of the canonical split graph is an original vertex together
with one connected component of its link. -/
def SplitVertex (G : SimpleGraph V) :=
  Σ v : V, (G.triangleLink v).ConnectedComponent

noncomputable instance instDecidableRelTriangleLink
    (G : SimpleGraph V) (v : V) :
    DecidableRel (G.triangleLink v).Adj :=
  Classical.decRel _

noncomputable instance instFintypeSplitVertex (G : SimpleGraph V) :
    Fintype G.SplitVertex := by
  classical
  unfold SplitVertex
  infer_instance

noncomputable instance instDecidableEqSplitVertex (G : SimpleGraph V) :
    DecidableEq G.SplitVertex :=
  Classical.decEq G.SplitVertex

/-- The split copy of `u` selected by the original edge `uv`. -/
def splitEndpoint (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    G.SplitVertex :=
  ⟨u, (G.triangleLink u).connectedComponentMk ⟨v, huv⟩⟩

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem splitEndpoint_fst (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) : (G.splitEndpoint huv).1 = u :=
  rfl

/-- The canonical graph obtained by splitting every vertex along the
components of its link. -/
def splitGraph (G : SimpleGraph V) : SimpleGraph G.SplitVertex where
  Adj a b := ∃ huv : G.Adj a.1 b.1,
    a.2 = (G.triangleLink a.1).connectedComponentMk ⟨b.1, huv⟩ ∧
    b.2 = (G.triangleLink b.1).connectedComponentMk
      ⟨a.1, G.symm.symm _ _ huv⟩
  symm.symm := by
    rintro a b ⟨hab, ha, hb⟩
    refine ⟨G.symm.symm _ _ hab, ?_, ?_⟩
    · simpa using hb
    · simpa using ha
  loopless.irrefl := by
    rintro a ⟨haa, ha, hb⟩
    exact G.loopless.irrefl a.1 haa

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem splitGraph_adj_iff (G : SimpleGraph V) {a b : G.SplitVertex} :
    G.splitGraph.Adj a b ↔ ∃ huv : G.Adj a.1 b.1,
      a.2 = (G.triangleLink a.1).connectedComponentMk ⟨b.1, huv⟩ ∧
      b.2 = (G.triangleLink b.1).connectedComponentMk
        ⟨a.1, G.symm.symm _ _ huv⟩ :=
  Iff.rfl

omit [Fintype V] [DecidableEq V] in
/-- Every original edge has a corresponding edge between its selected split
endpoints. -/
theorem splitGraph_adj_splitEndpoints (G : SimpleGraph V)
    {u v : V} (huv : G.Adj u v) :
    G.splitGraph.Adj (G.splitEndpoint huv)
      (G.splitEndpoint (G.symm.symm _ _ huv)) := by
  refine ⟨huv, rfl, ?_⟩
  rfl

/-- Forgetting link components defines a graph homomorphism from the split
graph to the original graph. -/
def splitProjection (G : SimpleGraph V) : G.splitGraph →g G where
  toFun a := a.1
  map_rel' := by
    rintro a b ⟨hab, ha, hb⟩
    exact hab

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem splitProjection_apply (G : SimpleGraph V) (a : G.SplitVertex) :
    G.splitProjection a = a.1 :=
  rfl

/-- Project a finite split-vertex set to its original vertices. -/
noncomputable def projectSplitVertexSet (G : SimpleGraph V)
    (s : Finset G.SplitVertex) : Finset V :=
  s.image fun a ↦ a.1

omit [Fintype V] [DecidableEq V] in
/-- Projection is injective on every clique of the split graph. -/
theorem injOn_fst_of_isClique_splitGraph (G : SimpleGraph V)
    {s : Finset G.SplitVertex} (hs : G.splitGraph.IsClique s) :
    Set.InjOn (fun a : G.SplitVertex ↦ a.1) (s : Set G.SplitVertex) := by
  intro a ha b hb hab
  by_contra hne
  obtain ⟨hadj, hcomponentA, hcomponentB⟩ := hs ha hb hne
  change a.1 = b.1 at hab
  rw [hab] at hadj
  exact G.loopless.irrefl b.1 hadj

/-- Projecting a split triangle gives an original graph triangle of the same
cardinality. -/
theorem projectSplitVertexSet_mem_triangles (G : SimpleGraph V)
    {t : Finset G.SplitVertex} (ht : t ∈ G.splitGraph.triangles) :
    G.projectSplitVertexSet t ∈ G.triangles := by
  classical
  have htClique : G.splitGraph.IsNClique 3 t := by
    simpa [triangles] using ht
  have hprojectClique : G.IsClique (G.projectSplitVertexSet t) := by
    intro u hu v hv huv
    obtain ⟨a, hat, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hbt, rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by
      intro hab
      exact huv (congrArg Sigma.fst hab)
    exact (htClique.isClique hat hbt hab).choose
  have hprojectCard : (G.projectSplitVertexSet t).card = 3 := by
    rw [projectSplitVertexSet, Finset.card_image_iff.mpr
      (G.injOn_fst_of_isClique_splitGraph htClique.isClique),
      htClique.card_eq]
  simpa [triangles] using (show G.IsNClique 3 (G.projectSplitVertexSet t) from
    ⟨hprojectClique, hprojectCard⟩)

omit [Fintype V] [DecidableEq V] in
/-- Two neighbors of `u` lying with `u` in a triangle select the same split
copy of `u`. -/
theorem splitEndpoint_eq_of_triangle (G : SimpleGraph V)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : G.Adj v w) :
    G.splitEndpoint huv = G.splitEndpoint huw := by
  change (⟨u, (G.triangleLink u).connectedComponentMk ⟨v, huv⟩⟩ :
      G.SplitVertex) =
    ⟨u, (G.triangleLink u).connectedComponentMk ⟨w, huw⟩⟩
  exact Sigma.ext rfl (heq_of_eq
    (ConnectedComponent.connectedComponentMk_eq_of_adj hvw))

/-- Every original triangle has a triangle lift in the canonical split graph,
and projecting that lift recovers the original vertex set. -/
theorem exists_split_triangle_project_eq (G : SimpleGraph V)
    {t : Finset V} (ht : t ∈ G.triangles) :
    ∃ q ∈ G.splitGraph.triangles, G.projectSplitVertexSet q = t := by
  classical
  have htClique : G.IsNClique 3 t := by
    simpa [triangles] using ht
  obtain ⟨u, v, w, huvNe, huwNe, hvwNe, rfl⟩ :=
    Finset.card_eq_three.mp htClique.card_eq
  have huv : G.Adj u v := htClique.isClique (by simp) (by simp) huvNe
  have huw : G.Adj u w := htClique.isClique (by simp) (by simp) huwNe
  have hvw : G.Adj v w := htClique.isClique (by simp) (by simp) hvwNe
  let a := G.splitEndpoint huv
  let b := G.splitEndpoint (G.symm.symm _ _ huv)
  let c := G.splitEndpoint (G.symm.symm _ _ huw)
  have hab : G.splitGraph.Adj a b := by
    simpa [a, b] using G.splitGraph_adj_splitEndpoints huv
  have hac : G.splitGraph.Adj a c := by
    have ha : G.splitEndpoint huv = G.splitEndpoint huw :=
      G.splitEndpoint_eq_of_triangle huv huw hvw
    change G.splitGraph.Adj (G.splitEndpoint huv)
      (G.splitEndpoint (G.symm.symm _ _ huw))
    rw [ha]
    exact G.splitGraph_adj_splitEndpoints huw
  have hbc : G.splitGraph.Adj b c := by
    have hb : G.splitEndpoint (G.symm.symm _ _ huv) =
        G.splitEndpoint hvw :=
      G.splitEndpoint_eq_of_triangle (G.symm.symm _ _ huv) hvw huw
    have hc : G.splitEndpoint (G.symm.symm _ _ huw) =
        G.splitEndpoint (G.symm.symm _ _ hvw) :=
      G.splitEndpoint_eq_of_triangle (G.symm.symm _ _ huw)
        (G.symm.symm _ _ hvw) huv
    change G.splitGraph.Adj
      (G.splitEndpoint (G.symm.symm _ _ huv))
      (G.splitEndpoint (G.symm.symm _ _ huw))
    rw [hb, hc]
    exact G.splitGraph_adj_splitEndpoints hvw
  have habNe : a ≠ b := by
    intro h
    exact huvNe (congrArg Sigma.fst h)
  have hacNe : a ≠ c := by
    intro h
    exact huwNe (congrArg Sigma.fst h)
  have hbcNe : b ≠ c := by
    intro h
    exact hvwNe (congrArg Sigma.fst h)
  let q : Finset G.SplitVertex := {a, b, c}
  have hqClique : G.splitGraph.IsClique q := by
    dsimp only [q]
    simp only [Finset.coe_insert, Finset.coe_singleton]
    rw [isClique_insert]
    constructor
    · rw [isClique_pair]
      exact fun _ ↦ hbc
    · intro x hx hax
      rcases hx with rfl | rfl
      · exact hab
      · exact hac
  have hqCard : q.card = 3 := by
    simp [q, habNe, hacNe, hbcNe]
  have hqTriangle : q ∈ G.splitGraph.triangles := by
    simpa [triangles] using (show G.splitGraph.IsNClique 3 q from
      ⟨hqClique, hqCard⟩)
  refine ⟨q, hqTriangle, ?_⟩
  simp [projectSplitVertexSet, q, a, b, c]

end SimpleGraph
