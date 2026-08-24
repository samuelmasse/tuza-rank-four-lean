import TuzaRankFour.ResidualIndependence

/-!
# Transfer ledger and the final crown inequality

The component transfer depletes selected labelled edges and credits their
spanners.  This file records exactly the properties later arguments use and
proves the final Hall/crown cardinal inequality independently of how the
ledger is constructed.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The auditable output required from the componentwise charge transfer. -/
structure LabelledTransferLedger (G : SimpleGraph V)
    (S : Finset (Finset V)) where
  depletedEdges : Finset (Finset V)
  creditedVertices : Finset V
  depleted_subset : depletedEdges ⊆ G.labelledPackingEdges S
  depleted_spanners_credited :
    ∀ ⦃e⦄, e ∈ depletedEdges →
      G.packingEdgeSpanners S e ⊆ creditedVertices
  depleted_owned_by_prettyGood :
    ∀ ⦃e⦄, e ∈ depletedEdges →
      ∃ t ∈ G.prettyGoodPackingTriangles S, e ⊆ t

/-- Labelled edges retaining their final unit after the component transfer. -/
noncomputable def LabelledTransferLedger.remainingEdges
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (D : G.LabelledTransferLedger S) : Finset (Finset V) :=
  G.labelledPackingEdges S \ D.depletedEdges

@[simp]
theorem LabelledTransferLedger.mem_remainingEdges_iff
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (D : G.LabelledTransferLedger S) {e : Finset V} :
    e ∈ D.remainingEdges ↔
      e ∈ G.labelledPackingEdges S ∧ e ∉ D.depletedEdges := by
  classical
  simp [LabelledTransferLedger.remainingEdges]

/-- An uncredited outside vertex can span only an edge whose unit remains. -/
theorem LabelledTransferLedger.mem_remainingEdges_of_spans_outside_uncredited
    {G : SimpleGraph V} {S : Finset (Finset V)}
    (D : G.LabelledTransferLedger S)
    (hS : G.IsSupportMaximalPacking S)
    {c : V} (hcOutside : c ∉ triangleFamilyVertexSupport S)
    (hcUncredited : c ∉ D.creditedVertices)
    {e : Finset V} (hce : G.Spans c e) :
    e ∈ D.remainingEdges := by
  classical
  rw [D.mem_remainingEdges_iff]
  refine ⟨G.mem_labelledPackingEdges_of_spans_outside hS hcOutside hce, ?_⟩
  intro heDepleted
  have hcSpanner : c ∈ G.packingEdgeSpanners S e := by
    rw [G.mem_packingEdgeSpanners_iff]
    exact ⟨hcOutside, hce.2⟩
  exact hcUncredited (D.depleted_spanners_credited heDepleted hcSpanner)

/-- If a residual independent family spans only remaining labelled edges,
then absence of a nonempty crown forces at least as many remaining edges as
residual vertices. -/
theorem card_le_remainingEdges_of_no_fatHeadCrown
    (G : SimpleGraph V) {S : Finset (Finset V)}
    (D : G.LabelledTransferLedger S)
    (hTriangleSupport : G.triangleSupport = G)
    {I : Finset V} (hIIndependent : G.IsIndepSet (I : Set V))
    (hINotLabelled : Disjoint I (G.labelledPackingVertices S))
    (hISpans : ∀ c ∈ I, ∃ e : Finset V, G.Spans c e)
    (hISpansRemaining : ∀ c ∈ I, ∀ ⦃e : Finset V⦄,
      G.Spans c e → e ∈ D.remainingEdges)
    (hNoCrown : ¬∃ K : G.FatHeadCrown, K.headEdges.Nonempty) :
    I.card ≤ D.remainingEdges.card := by
  classical
  rcases G.exists_injective_spanner_or_deficient_subfamily S I with
      hInjective | hDeficient
  · obtain ⟨f, hfInjective, hfSpans⟩ := hInjective
    let g : {c : V // c ∈ I} → {e : Finset V // e ∈ D.remainingEdges} :=
      fun c ↦ ⟨(f c).1, hISpansRemaining c.1 c.2 (hfSpans c)⟩
    have hgInjective : Function.Injective g := by
      intro c d hcd
      apply hfInjective
      apply Subtype.ext
      have hval := congrArg
        (fun z : {e : Finset V // e ∈ D.remainingEdges} ↦ z.1) hcd
      simpa [g] using hval
    have hcard := Fintype.card_le_of_injective g hgInjective
    simpa only [Fintype.card_coe] using hcard
  · obtain ⟨A, hA⟩ := hDeficient
    have hSpansLabelled : ∀ c ∈ I, ∀ ⦃e : Finset V⦄,
        G.Spans c e → e ∈ G.labelledPackingEdges S := by
      intro c hcI e hce
      exact (D.mem_remainingEdges_iff.mp
        (hISpansRemaining c hcI hce)).1
    obtain ⟨K, hKnonempty⟩ :=
      G.exists_nonempty_fatHeadCrown_of_deficient_independent_spanners
        hTriangleSupport hIIndependent hINotLabelled hSpansLabelled
        hISpans hA
    exact (hNoCrown ⟨K, hKnonempty⟩).elim

end SimpleGraph
