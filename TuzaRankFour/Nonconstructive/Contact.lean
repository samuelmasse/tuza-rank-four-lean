import TuzaRankFour.Nonconstructive.Definitions

/-!
# Source-bound packing owners and contact closure

All definitions in this file are parameterized by a single verified maximum
packing in a single source graph.  This prevents owner information from one
optimizer state from being reused with a different graph or packing witness.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A frozen maximum triangle-packing witness in one source graph. -/
structure MaximumTrianglePackingWitness (G : SimpleGraph V) where
  packing : Finset (Finset V)
  isPacking : G.IsTrianglePacking packing
  isMaximum : packing.card = G.trianglePackingNumber

/-- The packed triangles that share a literal ground edge with `t`.

For graph triangles, sharing a ground edge is equivalent to having vertex
intersection of cardinality at least two. -/
noncomputable def MaximumTrianglePackingWitness.owners
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (t : Finset V) : Finset (Finset V) := by
  classical
  exact W.packing.filter fun p => 2 ≤ (p ∩ t).card

@[simp]
theorem MaximumTrianglePackingWitness.mem_owners_iff
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    {p t : Finset V} :
    p ∈ W.owners t ↔ p ∈ W.packing ∧ 2 ≤ (p ∩ t).card := by
  classical
  simp [MaximumTrianglePackingWitness.owners]

/-- A source triangle is a one-contact triangle when it has exactly one owner
in the frozen maximum packing. -/
def MaximumTrianglePackingWitness.IsOneContact
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (t : Finset V) : Prop :=
  t ∈ G.triangles ∧ (W.owners t).card = 1

/-- A source triangle is multi-contact when at least two frozen packing
members own literal ground edges of it. -/
def MaximumTrianglePackingWitness.IsMultiContact
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (t : Finset V) : Prop :=
  t ∈ G.triangles ∧ 2 ≤ (W.owners t).card

/-- A two-owner source triangle, called a brace in the current route. -/
def MaximumTrianglePackingWitness.IsBrace
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (t : Finset V) : Prop :=
  t ∈ G.triangles ∧ (W.owners t).card = 2

/-- A literal three-owner source triangle. -/
def MaximumTrianglePackingWitness.IsThreeOwner
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (t : Finset V) : Prop :=
  t ∈ G.triangles ∧ (W.owners t).card = 3

/-- Two distinct packed members are in contact when one source triangle is
owned by both of them. -/
def MaximumTrianglePackingWitness.AreInContact
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (p q : Finset V) : Prop :=
  p ≠ q ∧ ∃ t ∈ G.triangles, p ∈ W.owners t ∧ q ∈ W.owners t

theorem MaximumTrianglePackingWitness.areInContact_comm
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    {p q : Finset V} :
    W.AreInContact p q ↔ W.AreInContact q p := by
  constructor
  · rintro ⟨hpq, t, ht, hp, hq⟩
    exact ⟨hpq.symm, t, ht, hq, hp⟩
  · rintro ⟨hqp, t, ht, hq, hp⟩
    exact ⟨hqp.symm, t, ht, hp, hq⟩

/-- The complete literal source closure of a selected owner set `I`: every
source triangle with at least one owner in `I` is retained. -/
noncomputable def MaximumTrianglePackingWitness.contactClosure
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (I : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact G.triangles.filter fun t => (W.owners t ∩ I).Nonempty

@[simp]
theorem MaximumTrianglePackingWitness.mem_contactClosure_iff
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    {I : Finset (Finset V)} {t : Finset V} :
    t ∈ W.contactClosure I ↔
      t ∈ G.triangles ∧ (W.owners t ∩ I).Nonempty := by
  classical
  simp [MaximumTrianglePackingWitness.contactClosure]

/-- `I` is owner-closed when every source triangle touching an owner in `I`
has all of its frozen packing owners in `I`.

This is the closure property supplied by taking a whole component of the
packing-contact graph.  Connectivity is intentionally kept separate: local
blocker statements usually use owner closure and an explicit small contact
pattern, while a later unavoidability theorem must prove the component claim.
-/
def MaximumTrianglePackingWitness.IsOwnerClosed
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (I : Finset (Finset V)) : Prop :=
  I ⊆ W.packing ∧
    ∀ ⦃t⦄, t ∈ G.triangles →
      (W.owners t ∩ I).Nonempty → W.owners t ⊆ I

theorem MaximumTrianglePackingWitness.owners_subset_of_mem_contactClosure
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    {I : Finset (Finset V)} (hClosed : W.IsOwnerClosed I)
    {t : Finset V} (ht : t ∈ W.contactClosure I) :
    W.owners t ⊆ I := by
  have htData := W.mem_contactClosure_iff.mp ht
  exact hClosed.2 htData.1 htData.2

/-- The literal packed ground edges belonging to the selected owner set. -/
noncomputable def MaximumTrianglePackingWitness.packingEdgeSupport
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness)
    (I : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact I.biUnion fun p => p.powersetCard 2

/-- A source-bound contact region packages the selected owners and their
whole-component closure proof without adding any local blocker conclusion. -/
structure MaximumTrianglePackingWitness.ContactRegion
    {G : SimpleGraph V} (W : G.MaximumTrianglePackingWitness) where
  members : Finset (Finset V)
  nonempty : members.Nonempty
  ownerClosed : W.IsOwnerClosed members

end SimpleGraph
