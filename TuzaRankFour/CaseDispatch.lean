import TuzaRankFour.Certificates.Semantic.AllCases
import TuzaRankFour.PackingExtraction

/-!
# Dispatch from canonical four-packings to the certified finite endpoints
 -/

namespace TuzaRankFour.CaseDispatch

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.FiniteEncoding
open TuzaRankFour.SemanticEncoding
open TuzaRankFour.PackingClassification

def markedMatchesBool (n : Nat) (s : Fin 16) (marked : List Nat) : Bool :=
  marked.all fun index =>
    decide (∃ b : Block, ∃ t : Fin n × Fin n × Fin n,
      (orderedTriangles n)[index]? = some t ∧
        triangleFinset t = canonicalBlockFin n s b)

theorem markedMatchesBool_eq_true_iff (n : Nat) (s : Fin 16)
    (marked : List Nat) :
    markedMatchesBool n s marked = true ↔
      ∀ index, List.Mem index marked →
        ∃ b : Block, ∃ t : Fin n × Fin n × Fin n,
          (orderedTriangles n)[index]? = some t ∧
            triangleFinset t = canonicalBlockFin n s b := by
  simp [markedMatchesBool]
  constructor
  · intro h index hindex
    exact h index hindex
  · intro h index hindex
    exact h index hindex

theorem markedTriangles_of_matches {n : Nat} {s : Fin 16}
    {marked : List Nat} {G : SimpleGraph (Fin n)}
    (hMatches : markedMatchesBool n s marked = true)
    (hCanonical : ∀ b, canonicalBlockFin n s b ∈ G.triangles) :
    ∀ index, List.Mem index marked →
      ∃ t, (orderedTriangles n)[index]? = some t ∧
        triangleFinset t ∈ G.triangles := by
  intro index hindex
  obtain ⟨b, t, ht, hblock⟩ :=
    (markedMatchesBool_eq_true_iff n s marked).mp hMatches index hindex
  exact ⟨t, ht, hblock.symm ▸ hCanonical b⟩

theorem no_rank_four_counterexample_six
    (G : SimpleGraph (Fin 6))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 6, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_six hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 6, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order06Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order06Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_seven
    (G : SimpleGraph (Fin 7))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 7, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_seven hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 7, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order07Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order07Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order07Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order07Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order07Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order07Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_eight
    (G : SimpleGraph (Fin 8))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 8, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_eight hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 8, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton03.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton03.markedPacking)
        (s := (3 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton04.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton04.markedPacking)
        (s := (4 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order08Skeleton05.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order08Skeleton05.markedPacking)
        (s := (5 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_nine
    (G : SimpleGraph (Fin 9))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 9, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_nine hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 9, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton03.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton03.markedPacking)
        (s := (3 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton04.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton04.markedPacking)
        (s := (4 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton05.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton05.markedPacking)
        (s := (5 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton06.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton06.markedPacking)
        (s := (6 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton07.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton07.markedPacking)
        (s := (7 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton08.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton08.markedPacking)
        (s := (8 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton09.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton09.markedPacking)
        (s := (9 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order09Skeleton10.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order09Skeleton10.markedPacking)
        (s := (10 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_ten
    (G : SimpleGraph (Fin 10))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 10, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_ten hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 10, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton03.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton03.markedPacking)
        (s := (3 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton04.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton04.markedPacking)
        (s := (4 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton05.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton05.markedPacking)
        (s := (5 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton06.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton06.markedPacking)
        (s := (6 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton07.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton07.markedPacking)
        (s := (7 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton08.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton08.markedPacking)
        (s := (8 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton09.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton09.markedPacking)
        (s := (9 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton10.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton10.markedPacking)
        (s := (10 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton11.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton11.markedPacking)
        (s := (11 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton12.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton12.markedPacking)
        (s := (12 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order10Skeleton13.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order10Skeleton13.markedPacking)
        (s := (13 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_eleven
    (G : SimpleGraph (Fin 11))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 11, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_eleven hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 11, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton03.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton03.markedPacking)
        (s := (3 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton04.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton04.markedPacking)
        (s := (4 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton05.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton05.markedPacking)
        (s := (5 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton06.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton06.markedPacking)
        (s := (6 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton07.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton07.markedPacking)
        (s := (7 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton08.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton08.markedPacking)
        (s := (8 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton09.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton09.markedPacking)
        (s := (9 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton10.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton10.markedPacking)
        (s := (10 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton11.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton11.markedPacking)
        (s := (11 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton12.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton12.markedPacking)
        (s := (12 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton13.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton13.markedPacking)
        (s := (13 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order11Skeleton14.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order11Skeleton14.markedPacking)
        (s := (14 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · norm_num [canonicalOrder, canonicalOrders] at hfit

theorem no_rank_four_counterexample_twelve
    (G : SimpleGraph (Fin 12))
    (hSupport : G.triangleSupport = G)
    (hVertices : ∀ v : Fin 12, v ∈ G.triangleSupportVertices)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) : False := by
  obtain ⟨s, e, hfit, hCanonical⟩ := G.exists_canonical_four_packing_twelve hν
  let H := G.map e.toEmbedding
  have hSupportH : H.triangleSupport = H := by
    change (G.map e.toEmbedding).triangleSupport = G.map e.toEmbedding
    exact G.map_equiv_triangleSupported e hSupport
  have hVerticesH : ∀ v : Fin 12, v ∈ H.triangleSupportVertices := by
    change ∀ v, v ∈ (G.map e.toEmbedding).triangleSupportVertices
    exact G.map_equiv_all_vertices_triangleSupported e hVertices
  have hνH : H.trianglePackingNumber ≤ 4 := by
    change (G.map e.toEmbedding).trianglePackingNumber ≤ 4
    rw [G.trianglePackingNumber_map_equiv e, hν]
  have hτH : 8 < H.triangleTransversalNumber := by
    change 8 < (G.map e.toEmbedding).triangleTransversalNumber
    rw [G.triangleTransversalNumber_map_equiv e]
    exact hτ
  fin_cases s
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton00.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton00.markedPacking)
        (s := (0 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton01.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton01.markedPacking)
        (s := (1 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton02.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton02.markedPacking)
        (s := (2 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton03.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton03.markedPacking)
        (s := (3 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton04.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton04.markedPacking)
        (s := (4 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton05.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton05.markedPacking)
        (s := (5 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton06.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton06.markedPacking)
        (s := (6 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton07.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton07.markedPacking)
        (s := (7 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton08.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton08.markedPacking)
        (s := (8 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton09.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton09.markedPacking)
        (s := (9 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton10.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton10.markedPacking)
        (s := (10 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton11.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton11.markedPacking)
        (s := (11 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton12.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton12.markedPacking)
        (s := (12 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton13.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton13.markedPacking)
        (s := (13 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton14.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton14.markedPacking)
        (s := (14 : Fin 16)) (by decide) hCanonical)
      hνH hτH
  · exact TuzaRankFour.Certificates.Semantic.Order12Skeleton15.no_counterexample
      H hSupportH hVerticesH
      (markedTriangles_of_matches
        (G := H)
        (marked := TuzaRankFour.Certificates.Semantic.Order12Skeleton15.markedPacking)
        (s := (15 : Fin 16)) (by decide) hCanonical)
      hνH hτH

end TuzaRankFour.CaseDispatch
