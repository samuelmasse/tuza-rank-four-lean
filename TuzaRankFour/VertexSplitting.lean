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

omit [Fintype V] [DecidableEq V] in
/-- Adjacent split vertices with the same ordered pair of original endpoints
are equal. -/
theorem eq_of_splitGraph_adj_of_fst_eq (G : SimpleGraph V)
    {a b c d : G.SplitVertex}
    (hac : G.splitGraph.Adj a c) (hbd : G.splitGraph.Adj b d)
    (hab : a.1 = b.1) (hcd : c.1 = d.1) : a = b := by
  rcases a with ⟨av, ac⟩
  rcases b with ⟨bv, bc⟩
  rcases c with ⟨cv, cc⟩
  rcases d with ⟨dv, dc⟩
  simp only at hab hcd
  subst bv
  subst dv
  rcases hac with ⟨h₁, ha, hc⟩
  rcases hbd with ⟨h₂, hb, hd⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact ha.trans (by simpa using hb.symm)

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

/-- Projection is injective on the set of split triangles. -/
theorem projectSplitVertexSet_injective_on_triangles (G : SimpleGraph V)
    {q r : Finset G.SplitVertex}
    (hq : q ∈ G.splitGraph.triangles)
    (hr : r ∈ G.splitGraph.triangles)
    (hproject : G.projectSplitVertexSet q = G.projectSplitVertexSet r) :
    q = r := by
  classical
  have hqClique : G.splitGraph.IsNClique 3 q := by
    simpa [triangles] using hq
  have hrClique : G.splitGraph.IsNClique 3 r := by
    simpa [triangles] using hr
  apply Finset.Subset.antisymm
  · intro a ha
    have haProject : a.1 ∈ G.projectSplitVertexSet q :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [hproject] at haProject
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haProject
    have hother : ∃ c ∈ q, c ≠ a := by
      by_contra h
      push Not at h
      have hsub : q ⊆ {a} := by
        intro c hc
        simp [h c hc]
      have hcard := Finset.card_le_card hsub
      simp [hqClique.card_eq] at hcard
    obtain ⟨c, hc, hca⟩ := hother
    have hcProject : c.1 ∈ G.projectSplitVertexSet q :=
      Finset.mem_image.mpr ⟨c, hc, rfl⟩
    rw [hproject] at hcProject
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hcProject
    have hac : G.splitGraph.Adj a c :=
      hqClique.isClique ha hc hca.symm
    have hbdNe : b ≠ d := by
      intro hbd
      subst d
      obtain ⟨hOriginal, hcompA, hcompC⟩ := hac
      apply G.loopless.irrefl a.1
      have hfst : a.1 = c.1 := hba.symm.trans hdc
      simpa [hfst] using hOriginal
    have hbd : G.splitGraph.Adj b d :=
      hrClique.isClique hb hd hbdNe
    have habEq : a = b :=
      G.eq_of_splitGraph_adj_of_fst_eq hac hbd hba.symm hdc.symm
    simpa [habEq] using hb
  · intro a ha
    have haProject : a.1 ∈ G.projectSplitVertexSet r :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [← hproject] at haProject
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haProject
    have hother : ∃ c ∈ r, c ≠ a := by
      by_contra h
      push Not at h
      have hsub : r ⊆ {a} := by
        intro c hc
        simp [h c hc]
      have hcard := Finset.card_le_card hsub
      simp [hrClique.card_eq] at hcard
    obtain ⟨c, hc, hca⟩ := hother
    have hcProject : c.1 ∈ G.projectSplitVertexSet r :=
      Finset.mem_image.mpr ⟨c, hc, rfl⟩
    rw [← hproject] at hcProject
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hcProject
    have hac : G.splitGraph.Adj a c :=
      hrClique.isClique ha hc hca.symm
    have hbdNe : b ≠ d := by
      intro hbd
      subst d
      obtain ⟨hOriginal, hcompA, hcompC⟩ := hac
      apply G.loopless.irrefl a.1
      have hfst : a.1 = c.1 := hba.symm.trans hdc
      simpa [hfst] using hOriginal
    have hbd : G.splitGraph.Adj b d :=
      hqClique.isClique hb hd hbdNe
    have habEq : a = b :=
      G.eq_of_splitGraph_adj_of_fst_eq hac hbd hba.symm hdc.symm
    simpa [habEq] using hb

/-- For two split triangles, projection preserves whether their intersection
has cardinality at most one.  This is the edge-disjointness relation used in
triangle packings. -/
theorem card_inter_projectSplitVertexSet_le_one_iff (G : SimpleGraph V)
    {q r : Finset G.SplitVertex}
    (hq : q ∈ G.splitGraph.triangles)
    (hr : r ∈ G.splitGraph.triangles) :
    ((G.projectSplitVertexSet q ∩ G.projectSplitVertexSet r).card ≤ 1) ↔
      (q ∩ r).card ≤ 1 := by
  classical
  have hqClique : G.splitGraph.IsNClique 3 q := by
    simpa [triangles] using hq
  have hrClique : G.splitGraph.IsNClique 3 r := by
    simpa [triangles] using hr
  constructor
  · intro hproject
    rw [Finset.card_le_one_iff] at hproject ⊢
    intro a b ha hb
    simp only [Finset.mem_inter] at ha hb
    apply G.injOn_fst_of_isClique_splitGraph hqClique.isClique ha.1 hb.1
    apply hproject
    · simp only [Finset.mem_inter]
      exact ⟨Finset.mem_image.mpr ⟨a, ha.1, rfl⟩,
        Finset.mem_image.mpr ⟨a, ha.2, rfl⟩⟩
    · simp only [Finset.mem_inter]
      exact ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩,
        Finset.mem_image.mpr ⟨b, hb.2, rfl⟩⟩
  · intro hsplit
    rw [Finset.card_le_one_iff] at hsplit ⊢
    intro u v hu hv
    simp only [Finset.mem_inter] at hu hv
    obtain ⟨a, haq, hau⟩ := Finset.mem_image.mp hu.1
    obtain ⟨c, hcr, hcu⟩ := Finset.mem_image.mp hu.2
    obtain ⟨b, hbq, hbv⟩ := Finset.mem_image.mp hv.1
    obtain ⟨d, hdr, hdv⟩ := Finset.mem_image.mp hv.2
    by_cases hab : a = b
    · exact hau.symm.trans ((congrArg Sigma.fst hab).trans hbv)
    have habAdj : G.splitGraph.Adj a b :=
      hqClique.isClique haq hbq hab
    have hcd : c ≠ d := by
      intro h
      have habFst : a.1 = b.1 := hau.trans (hcu.symm.trans
        ((congrArg Sigma.fst h).trans (hdv.trans hbv.symm)))
      apply G.loopless.irrefl b.1
      simpa [habFst] using habAdj.choose
    have hcdAdj : G.splitGraph.Adj c d :=
      hrClique.isClique hcr hdr hcd
    have hac : a = c := G.eq_of_splitGraph_adj_of_fst_eq habAdj hcdAdj
      (hau.trans hcu.symm) (hbv.trans hdv.symm)
    have hbd : b = d := G.eq_of_splitGraph_adj_of_fst_eq
      (G.splitGraph.symm.symm _ _ habAdj)
      (G.splitGraph.symm.symm _ _ hcdAdj)
      (hbv.trans hdv.symm) (hau.trans hcu.symm)
    have haInter : a ∈ q ∩ r := by
      simp only [Finset.mem_inter]
      exact ⟨haq, by simpa [hac] using hcr⟩
    have hbInter : b ∈ q ∩ r := by
      simp only [Finset.mem_inter]
      exact ⟨hbq, by simpa [hbd] using hdr⟩
    have hab' : a = b := hsplit haInter hbInter
    exact hau.symm.trans ((congrArg Sigma.fst hab').trans hbv)

/-- The canonical lift of an original triangle.  The preceding existence and
uniqueness theorems make the arbitrary choice extensionally irrelevant on
actual triangles. -/
noncomputable def liftTriangle (G : SimpleGraph V) (t : Finset V) :
    Finset G.SplitVertex :=
  if ht : t ∈ G.triangles then
    Classical.choose (G.exists_split_triangle_project_eq ht)
  else ∅

theorem liftTriangle_mem_triangles (G : SimpleGraph V)
    {t : Finset V} (ht : t ∈ G.triangles) :
    G.liftTriangle t ∈ G.splitGraph.triangles := by
  classical
  rw [liftTriangle, dif_pos ht]
  exact (Classical.choose_spec (G.exists_split_triangle_project_eq ht)).1

@[simp]
theorem projectSplitVertexSet_liftTriangle (G : SimpleGraph V)
    {t : Finset V} (ht : t ∈ G.triangles) :
    G.projectSplitVertexSet (G.liftTriangle t) = t := by
  classical
  rw [liftTriangle, dif_pos ht]
  exact (Classical.choose_spec (G.exists_split_triangle_project_eq ht)).2

/-- Project every triangle in a family from the split graph. -/
noncomputable def projectSplitTriangleFamily (G : SimpleGraph V)
    (P : Finset (Finset G.SplitVertex)) : Finset (Finset V) :=
  P.image G.projectSplitVertexSet

/-- Lift every triangle in a family to the split graph. -/
noncomputable def liftTriangleFamily (G : SimpleGraph V)
    (P : Finset (Finset V)) : Finset (Finset G.SplitVertex) :=
  P.image G.liftTriangle

/-- Projecting a triangle packing gives a triangle packing. -/
theorem isTrianglePacking_projectSplitTriangleFamily (G : SimpleGraph V)
    {P : Finset (Finset G.SplitVertex)}
    (hP : G.splitGraph.IsTrianglePacking P) :
    G.IsTrianglePacking (G.projectSplitTriangleFamily P) := by
  classical
  constructor
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact G.projectSplitVertexSet_mem_triangles (hP.1 hq)
  · intro s hs t ht hst
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    apply (G.card_inter_projectSplitVertexSet_le_one_iff
      (hP.1 hq) (hP.1 hr)).mpr
    apply hP.2 hq hr
    intro hqr
    subst r
    exact hst rfl

theorem card_projectSplitTriangleFamily (G : SimpleGraph V)
    {P : Finset (Finset G.SplitVertex)}
    (hP : G.splitGraph.IsTrianglePacking P) :
    (G.projectSplitTriangleFamily P).card = P.card := by
  classical
  rw [projectSplitTriangleFamily, Finset.card_image_iff.mpr]
  intro q hq r hr hproject
  exact G.projectSplitVertexSet_injective_on_triangles
    (hP.1 hq) (hP.1 hr) hproject

/-- Lifting a triangle packing gives a triangle packing. -/
theorem isTrianglePacking_liftTriangleFamily (G : SimpleGraph V)
    {P : Finset (Finset V)} (hP : G.IsTrianglePacking P) :
    G.splitGraph.IsTrianglePacking (G.liftTriangleFamily P) := by
  classical
  constructor
  · intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    exact G.liftTriangle_mem_triangles (hP.1 ht)
  · intro q hq r hr hqr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    have hsTriangle := hP.1 hs
    have htTriangle := hP.1 ht
    apply (G.card_inter_projectSplitVertexSet_le_one_iff
      (G.liftTriangle_mem_triangles hsTriangle)
      (G.liftTriangle_mem_triangles htTriangle)).mp
    simp only [G.projectSplitVertexSet_liftTriangle hsTriangle,
      G.projectSplitVertexSet_liftTriangle htTriangle]
    apply hP.2 hs ht
    intro hst
    subst t
    exact hqr rfl

theorem card_liftTriangleFamily (G : SimpleGraph V)
    {P : Finset (Finset V)} (hP : G.IsTrianglePacking P) :
    (G.liftTriangleFamily P).card = P.card := by
  classical
  rw [liftTriangleFamily, Finset.card_image_iff.mpr]
  intro s hs t ht hlift
  have hsTriangle := hP.1 hs
  have htTriangle := hP.1 ht
  have hproject := congrArg G.projectSplitVertexSet hlift
  simpa only [G.projectSplitVertexSet_liftTriangle hsTriangle,
    G.projectSplitVertexSet_liftTriangle htTriangle] using hproject

/-- Canonical vertex splitting preserves the triangle-packing number. -/
theorem trianglePackingNumber_splitGraph (G : SimpleGraph V) :
    G.splitGraph.trianglePackingNumber = G.trianglePackingNumber := by
  apply Nat.le_antisymm
  · rw [G.splitGraph.trianglePackingNumber_le_iff]
    intro P hP
    have hbound := G.card_le_trianglePackingNumber
      (G.isTrianglePacking_projectSplitTriangleFamily hP)
    simpa [G.card_projectSplitTriangleFamily hP] using hbound
  · rw [G.trianglePackingNumber_le_iff]
    intro P hP
    have hbound := G.splitGraph.card_le_trianglePackingNumber
      (G.isTrianglePacking_liftTriangleFamily hP)
    simpa [G.card_liftTriangleFamily hP] using hbound

/-- Projecting an edge of the split graph gives an edge of the original
graph. -/
theorem projectSplitVertexSet_mem_edges (G : SimpleGraph V)
    {e : Finset G.SplitVertex} (he : e ∈ G.splitGraph.edges) :
    G.projectSplitVertexSet e ∈ G.edges := by
  classical
  have heClique : G.splitGraph.IsNClique 2 e := by
    simpa [edges] using he
  have hprojectClique : G.IsClique (G.projectSplitVertexSet e) := by
    intro u hu v hv huv
    obtain ⟨a, hae, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hbe, rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by
      intro hab
      exact huv (congrArg Sigma.fst hab)
    exact (heClique.isClique hae hbe hab).choose
  have hprojectCard : (G.projectSplitVertexSet e).card = 2 := by
    rw [projectSplitVertexSet, Finset.card_image_iff.mpr
      (G.injOn_fst_of_isClique_splitGraph heClique.isClique),
      heClique.card_eq]
  simpa [edges] using (show G.IsNClique 2 (G.projectSplitVertexSet e) from
    ⟨hprojectClique, hprojectCard⟩)

/-- Project every edge in a split-graph family. -/
noncomputable def projectSplitEdgeFamily (G : SimpleGraph V)
    (C : Finset (Finset G.SplitVertex)) : Finset (Finset V) :=
  C.image G.projectSplitVertexSet

/-- A split-graph transversal projects to an original-graph transversal. -/
theorem isTriangleTransversal_projectSplitEdgeFamily (G : SimpleGraph V)
    {C : Finset (Finset G.SplitVertex)}
    (hC : G.splitGraph.IsTriangleTransversal C) :
    G.IsTriangleTransversal (G.projectSplitEdgeFamily C) := by
  classical
  constructor
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact G.projectSplitVertexSet_mem_edges (hC.1 hd)
  · intro t ht
    obtain ⟨q, hq, hproject⟩ := G.exists_split_triangle_project_eq ht
    obtain ⟨e, heC, heq⟩ := hC.2 hq
    refine ⟨G.projectSplitVertexSet e, Finset.mem_image.mpr ⟨e, heC, rfl⟩, ?_⟩
    intro u hu
    obtain ⟨a, hae, hau⟩ := Finset.mem_image.mp hu
    have haq : a ∈ q := heq hae
    have haProject : a.1 ∈ G.projectSplitVertexSet q :=
      Finset.mem_image.mpr ⟨a, haq, rfl⟩
    rw [hproject] at haProject
    simpa [hau] using haProject

omit [Fintype V] in
theorem card_projectSplitEdgeFamily_le (G : SimpleGraph V)
    (C : Finset (Finset G.SplitVertex)) :
    (G.projectSplitEdgeFamily C).card ≤ C.card := by
  classical
  exact Finset.card_image_le

/-- Canonical vertex splitting cannot decrease the minimum triangle
transversal number. -/
theorem triangleTransversalNumber_le_splitGraph (G : SimpleGraph V) :
    G.triangleTransversalNumber ≤
      G.splitGraph.triangleTransversalNumber := by
  obtain ⟨C, hC, hcard⟩ := G.splitGraph.exists_min_triangleTransversal
  calc
    G.triangleTransversalNumber ≤
        (G.projectSplitEdgeFamily C).card :=
      G.triangleTransversalNumber_le_card
        (G.isTriangleTransversal_projectSplitEdgeFamily hC)
    _ ≤ C.card := G.card_projectSplitEdgeFamily_le C
    _ = G.splitGraph.triangleTransversalNumber := hcard

/-- The connected link component carried by a split vertex maps onto that
vertex's entire link in the split graph. -/
def splitLinkComponentHom (G : SimpleGraph V) (a : G.SplitVertex) :
    a.2.toSimpleGraph →g G.splitGraph.triangleLink a where
  toFun x := by
    let b := G.splitEndpoint (G.symm.symm _ _ x.1.2)
    refine ⟨b, ?_⟩
    have ha : G.splitEndpoint x.1.2 = a := by
      rcases a with ⟨v, c⟩
      exact Sigma.ext rfl (heq_of_eq x.2)
    rw [← ha]
    exact G.splitGraph_adj_splitEndpoints x.1.2
  map_rel' := by
    intro x y hxy
    change G.splitGraph.Adj
      (G.splitEndpoint (G.symm.symm _ _ x.1.2))
      (G.splitEndpoint (G.symm.symm _ _ y.1.2))
    have hxyG : G.Adj x.1.1 y.1.1 := hxy
    have hx : G.splitEndpoint (G.symm.symm _ _ x.1.2) =
        G.splitEndpoint hxyG :=
      G.splitEndpoint_eq_of_triangle (G.symm.symm _ _ x.1.2)
        hxyG y.1.2
    have hy : G.splitEndpoint (G.symm.symm _ _ y.1.2) =
        G.splitEndpoint (G.symm.symm _ _ hxyG) :=
      G.splitEndpoint_eq_of_triangle (G.symm.symm _ _ y.1.2)
        (G.symm.symm _ _ hxyG) x.1.2
    rw [hx, hy]
    exact G.splitGraph_adj_splitEndpoints hxyG

omit [Fintype V] [DecidableEq V] in
theorem splitLinkComponentHom_surjective (G : SimpleGraph V)
    (a : G.SplitVertex) : Function.Surjective (G.splitLinkComponentHom a) := by
  intro b
  obtain ⟨hab, ha, hb⟩ := b.2
  let x0 : G.neighborSet a.1 := ⟨b.1.1, hab⟩
  have hx0 : x0 ∈ a.2.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact ha.symm
  let x : a.2.supp := ⟨x0, hx0⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change G.splitEndpoint (G.symm.symm _ _ hab) = b.1
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq hb.symm

/-- A single simultaneous canonical split makes every vertex link
preconnected. -/
theorem isSplitNormal_splitGraph (G : SimpleGraph V) :
    G.splitGraph.IsSplitNormal := by
  intro a
  exact a.2.connected_toSimpleGraph.preconnected.map
    (G.splitLinkComponentHom a) (G.splitLinkComponentHom_surjective a)

end SimpleGraph
