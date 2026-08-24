import TuzaRankFour.RankFourReduction
import TuzaRankFour.VertexSplitting

/-!
# The canonical rank-four kernel

This file assembles the exact reduction used before the twelve-vertex
discharge argument.  Starting from a graph, first discard edges outside all
triangles and then split every vertex along the connected components of its
triangle link.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The supported, canonically split graph used in the rank-four reduction. -/
noncomputable abbrev rankFourKernel (G : SimpleGraph V) :
    SimpleGraph G.triangleSupport.SplitVertex :=
  G.triangleSupport.splitGraph

@[simp]
theorem trianglePackingNumber_rankFourKernel (G : SimpleGraph V) :
    G.rankFourKernel.trianglePackingNumber = G.trianglePackingNumber := by
  rw [rankFourKernel, G.triangleSupport.trianglePackingNumber_splitGraph,
    G.trianglePackingNumber_triangleSupport]

/-- A transversal of the split kernel projects to the original graph. -/
theorem triangleTransversalNumber_le_rankFourKernel (G : SimpleGraph V) :
    G.triangleTransversalNumber ≤
      G.rankFourKernel.triangleTransversalNumber := by
  calc
    G.triangleTransversalNumber =
        G.triangleSupport.triangleTransversalNumber :=
      G.triangleTransversalNumber_triangleSupport.symm
    _ ≤ G.triangleSupport.splitGraph.triangleTransversalNumber :=
      G.triangleSupport.triangleTransversalNumber_le_splitGraph

theorem isSplitNormal_rankFourKernel (G : SimpleGraph V) :
    G.rankFourKernel.IsSplitNormal :=
  G.triangleSupport.isSplitNormal_splitGraph

theorem triangleSupport_rankFourKernel (G : SimpleGraph V) :
    G.rankFourKernel.triangleSupport = G.rankFourKernel :=
  G.triangleSupport_splitGraph_triangleSupport

theorem mem_triangleSupportVertices_rankFourKernel (G : SimpleGraph V)
    (a : G.triangleSupport.SplitVertex) :
    a ∈ G.rankFourKernel.triangleSupportVertices :=
  G.mem_triangleSupportVertices_splitGraph_triangleSupport a

/-- A strict rank-four counterexample kernel has no triangle-isolated `K₄`
edge block. -/
theorem rankFourKernel_no_triangleIsolatedK4 (G : SimpleGraph V)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber) :
    ∀ Q : Finset G.triangleSupport.SplitVertex,
      ¬G.rankFourKernel.IsTriangleIsolatedK4 Q := by
  have hνK : G.rankFourKernel.trianglePackingNumber = 4 := by
    simpa using G.trianglePackingNumber_rankFourKernel.trans hν
  have hτK : 2 * G.rankFourKernel.trianglePackingNumber <
      G.rankFourKernel.triangleTransversalNumber := by
    have hle := G.triangleTransversalNumber_le_rankFourKernel
    omega
  have hnone :=
    G.rankFourKernel.no_triangleIsolatedK4_of_rank_four_counterexample hνK hτK
  intro Q hQ
  exact hnone ⟨Q, hQ⟩

/-- A strict rank-four counterexample kernel has no nonempty fat-head crown. -/
theorem rankFourKernel_no_fatHeadCrown (G : SimpleGraph V)
    (hν : G.trianglePackingNumber = 4)
    (hτ : 8 < G.triangleTransversalNumber)
    (K : G.rankFourKernel.FatHeadCrown) :
    K.headEdges = ∅ := by
  have hνK : G.rankFourKernel.trianglePackingNumber = 4 := by
    simpa using G.trianglePackingNumber_rankFourKernel.trans hν
  have hτK : 2 * G.rankFourKernel.trianglePackingNumber <
      G.rankFourKernel.triangleTransversalNumber := by
    have hle := G.triangleTransversalNumber_le_rankFourKernel
    omega
  have hnone :=
    G.rankFourKernel.no_nonempty_fatHeadCrown_of_rank_four_counterexample hνK hτK
  by_contra hhead
  exact hnone ⟨K, Finset.nonempty_iff_ne_empty.mpr hhead⟩

end SimpleGraph
