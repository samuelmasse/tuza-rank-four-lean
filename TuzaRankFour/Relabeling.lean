import Mathlib.Combinatorics.SimpleGraph.Maps
import TuzaRankFour.Reduction

/-!
# Relabelling invariance

Triangle packings, triangle transversals, and the support conditions are
invariant under a bijective change of vertex labels.
-/

namespace SimpleGraph

set_option maxHeartbeats 0

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

theorem triangles_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).triangles =
      G.triangles.map ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩ := by
  classical
  ext s
  simp only [triangles, mem_cliqueFinset_iff, Finset.mem_map]
  change (G.map e.toEmbedding).IsNClique 3 s ↔
    ∃ a, G.IsNClique 3 a ∧ Finset.map e.toEmbedding a = s
  exact G.isNClique_map_iff (n := 3) (t := s) (f := e.toEmbedding) (by omega)

theorem edges_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).edges =
      G.edges.map ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩ := by
  classical
  ext s
  simp only [edges, mem_cliqueFinset_iff, Finset.mem_map]
  change (G.map e.toEmbedding).IsNClique 2 s ↔
    ∃ a, G.IsNClique 2 a ∧ Finset.map e.toEmbedding a = s
  exact G.isNClique_map_iff (n := 2) (t := s) (f := e.toEmbedding) (by omega)

theorem isTrianglePacking_map_equiv_iff (G : SimpleGraph V) (e : V ≃ W)
    (P : Finset (Finset V)) :
    (G.map e.toEmbedding).IsTrianglePacking
        (P.map e.finsetCongr.toEmbedding) ↔
      G.IsTrianglePacking P := by
  classical
  constructor
  · intro h
    constructor
    · intro s hs
      have hsMap := h.1 (Finset.mem_map.mpr ⟨s, hs, rfl⟩)
      rw [G.triangles_map_equiv e] at hsMap
      obtain ⟨t, ht, hEq⟩ := Finset.mem_map.mp hsMap
      have hts : t = s := e.finsetCongr.injective hEq
      simpa [hts] using ht
    · intro s hs t ht hst
      have hbound := h.2
        (Finset.mem_map.mpr ⟨s, hs, rfl⟩)
        (Finset.mem_map.mpr ⟨t, ht, rfl⟩)
        (by simpa using hst)
      simpa [Equiv.finsetCongr_apply, ← Finset.map_inter] using hbound
  · intro h
    constructor
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
      rw [G.triangles_map_equiv e]
      exact Finset.mem_map.mpr ⟨t, h.1 ht, rfl⟩
    · intro s hs t ht hst
      obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
      have hne : s' ≠ t' := by
        intro heq
        exact hst (congrArg e.finsetCongr heq)
      simpa [Equiv.finsetCongr_apply, ← Finset.map_inter] using
        h.2 hs' ht' hne

theorem trianglePackingNumber_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).trianglePackingNumber = G.trianglePackingNumber := by
  classical
  apply le_antisymm
  · rw [(G.map e.toEmbedding).trianglePackingNumber_le_iff]
    intro P hP
    let E : Finset (Finset V) ≃ Finset (Finset W) :=
      e.finsetCongr.finsetCongr
    let P' : Finset (Finset V) := E.symm P
    have hMap : P'.map e.finsetCongr.toEmbedding = P := by
      change E P' = P
      exact E.apply_symm_apply P
    have hP' : G.IsTrianglePacking P' := by
      rw [← G.isTrianglePacking_map_equiv_iff e P', hMap]
      exact hP
    have hcard : P'.card = P.card := by
      simp [P', E, Equiv.finsetCongr_apply]
    rw [← hcard]
    exact G.card_le_trianglePackingNumber hP'
  · rw [G.trianglePackingNumber_le_iff]
    intro P hP
    have hMap := (G.map e.toEmbedding).card_le_trianglePackingNumber
      ((G.isTrianglePacking_map_equiv_iff e P).mpr hP)
    simpa using hMap

theorem isTriangleTransversal_map_equiv_iff (G : SimpleGraph V) (e : V ≃ W)
    (C : Finset (Finset V)) :
    (G.map e.toEmbedding).IsTriangleTransversal
        (C.map e.finsetCongr.toEmbedding) ↔
      G.IsTriangleTransversal C := by
  classical
  constructor
  · intro h
    constructor
    · intro edge hedge
      have hMapped : e.finsetCongr edge ∈
          (G.map e.toEmbedding).edges := h.1
        (Finset.mem_map.mpr ⟨edge, hedge, rfl⟩)
      rw [G.edges_map_equiv e] at hMapped
      obtain ⟨source, hsource, hEq⟩ := Finset.mem_map.mp hMapped
      have : source = edge := e.finsetCongr.injective hEq
      simpa [this] using hsource
    · intro t ht
      have htMapped : e.finsetCongr t ∈
          (G.map e.toEmbedding).triangles := by
        rw [G.triangles_map_equiv e]
        exact Finset.mem_map.mpr ⟨t, ht, rfl⟩
      obtain ⟨edge, hedge, het⟩ := h.2 htMapped
      obtain ⟨source, hsource, hEq⟩ := Finset.mem_map.mp hedge
      refine ⟨source, hsource, ?_⟩
      rw [← hEq] at het
      simpa [Equiv.finsetCongr_apply, ← Finset.map_inter] using het
  · intro h
    constructor
    · intro edge hedge
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_map.mp hedge
      rw [G.edges_map_equiv e]
      exact Finset.mem_map.mpr ⟨source, h.1 hsource, rfl⟩
    · intro t ht
      rw [G.triangles_map_equiv e] at ht
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_map.mp ht
      obtain ⟨edge, hedge, het⟩ := h.2 hsource
      refine ⟨e.finsetCongr edge, Finset.mem_map.mpr ⟨edge, hedge, rfl⟩, ?_⟩
      simpa [Equiv.finsetCongr_apply, ← Finset.map_inter] using het

theorem triangleTransversalNumber_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).triangleTransversalNumber =
      G.triangleTransversalNumber := by
  classical
  apply le_antisymm
  · obtain ⟨C, hC, hcard⟩ := G.exists_min_triangleTransversal
    have hMapped := (G.map e.toEmbedding).triangleTransversalNumber_le_card
      ((G.isTriangleTransversal_map_equiv_iff e C).mpr hC)
    simpa [hcard] using hMapped
  · obtain ⟨C, hC, hcard⟩ :=
      (G.map e.toEmbedding).exists_min_triangleTransversal
    let E : Finset (Finset V) ≃ Finset (Finset W) :=
      e.finsetCongr.finsetCongr
    let C' : Finset (Finset V) := E.symm C
    have hMap : C'.map e.finsetCongr.toEmbedding = C := by
      change E C' = C
      exact E.apply_symm_apply C
    have hC' : G.IsTriangleTransversal C' := by
      rw [← G.isTriangleTransversal_map_equiv_iff e C', hMap]
      exact hC
    have hbound := G.triangleTransversalNumber_le_card hC'
    have hcard' : C'.card = C.card := by
      simp [C', E, Equiv.finsetCongr_apply]
    omega

theorem triangleSupport_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e.toEmbedding).triangleSupport =
      G.triangleSupport.map e.toEmbedding := by
  classical
  ext u v
  constructor
  · rintro ⟨t, ht, hu, hv, huv⟩
    rw [G.triangles_map_equiv e] at ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨a, ha, hau⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, hbv⟩ := Finset.mem_map.mp hv
    rw [map_adj]
    refine ⟨a, b, ⟨s, hs, ha, hb, ?_⟩, hau, hbv⟩
    intro hab
    apply huv
    rw [← hau, ← hbv, hab]
  · intro huv
    rw [map_adj] at huv
    obtain ⟨a, b, ⟨s, hs, ha, hb, hab⟩, hau, hbv⟩ := huv
    refine ⟨e.finsetCongr s, ?_, ?_, ?_, ?_⟩
    · rw [G.triangles_map_equiv e]
      exact Finset.mem_map.mpr ⟨s, hs, rfl⟩
    · exact Finset.mem_map.mpr ⟨a, ha, hau⟩
    · exact Finset.mem_map.mpr ⟨b, hb, hbv⟩
    · rw [← hau, ← hbv]
      exact e.injective.ne hab

theorem map_equiv_triangleSupported (G : SimpleGraph V) (e : V ≃ W)
    (hSupport : G.triangleSupport = G) :
    (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding := by
  rw [G.triangleSupport_map_equiv e, hSupport]

theorem map_equiv_all_vertices_triangleSupported (G : SimpleGraph V)
    (e : V ≃ W)
    (hVertices : ∀ v : V, v ∈ G.triangleSupportVertices) :
    ∀ w : W, w ∈ (G.map e.toEmbedding).triangleSupportVertices := by
  classical
  intro w
  obtain ⟨t, ht, hw⟩ := G.mem_triangleSupportVertices_iff.mp
    (hVertices (e.symm w))
  rw [(G.map e.toEmbedding).mem_triangleSupportVertices_iff]
  refine ⟨e.finsetCongr t, ?_, ?_⟩
  · rw [G.triangles_map_equiv e]
    exact Finset.mem_map.mpr ⟨t, ht, rfl⟩
  · simpa [Equiv.finsetCongr_apply] using hw

end SimpleGraph
