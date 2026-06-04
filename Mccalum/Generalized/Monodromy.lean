import Mccalum.Generalized.ComplexCovering
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy reduction toward `irreducible_section_single_root_deg` (M4)

This file collects the reusable kernel of the homotopy-deformation contradiction in the thesis proof
of Theorem 4.2.2 (the `d ≥ 2` case of `irreducible_section_single_root`). The thesis argument, given
the branched root-covering (`ComplexCovering.lean`) and Lemma 4.2.5 (transitive monodromy, cited from
Bochner–Martin), runs:

* a root-exchanging loop `Γ` (`Γ_h[α] = β`, `α ∈ D₁`, `β ∈ D₂`) is deformed within `U = {disc ≠ 0}`
  to a small loop `Γ''` around the section;
* the lift `φ''` of `Γ''` is a *continuous* path whose values are always roots of `h`, hence lie in
  the disjoint union of discs `⋃ⱼ Dⱼ`; since `φ''(0) = α ∈ D₁`, **`φ''` stays in `D₁`** (connectedness),
  so `φ''(1) ∈ D₁`, contradicting `φ''(1) = β ∈ D₂`.

The **confinement** step — a continuous path into a disjoint union of opens starting in one component
stays in it — is the genuine topological kernel and is proved here in full (`path_confined_to_open`,
`liftPath_confined`). The deformation of `Γ` to `Γ''` (two explicit homotopies in the thesis, codim-1
specific) and Lemma 4.2.5 itself remain the substantial geometric/foundational pieces of M4/M3.
-/

noncomputable section

open Set
open scoped Topology

/-- **Confinement to a connected component** (the topological kernel of the monodromy contradiction).

A continuous map from a *preconnected* space whose range lies in the union of two disjoint opens
`A ∪ B`, and which hits `A` at one point, lies entirely in `A`. Applied to a lifted path `φ` whose
values are roots confined to a disjoint union of discs, with `φ(0)` in one disc: `φ` never leaves it. -/
theorem path_confined_to_open {X : Type*} [TopologicalSpace X] {α : Type*} [TopologicalSpace α]
    [PreconnectedSpace α] (f : α → X) (hf : Continuous f)
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hsub : Set.range f ⊆ A ∪ B) {a₀ : α} (h₀ : f a₀ ∈ A) :
    ∀ a, f a ∈ A := by
  rcases (isPreconnected_range hf).subset_or_subset hA hB hAB hsub with h | h
  · exact fun a => h ⟨a, rfl⟩
  · exact absurd (h ⟨a₀, rfl⟩) (Set.disjoint_left.mp hAB h₀)

/-- **Endpoint confinement.** Under the hypotheses of `path_confined_to_open`, the value at any point
`a₁` lies in `A` and (since `A`, `B` are disjoint) is *not* in `B`. This is the exact shape used to
contradict `φ''(1) = β ∈ B` from `φ''(0) = α ∈ A`. -/
theorem path_endpoint_not_in_other {X : Type*} [TopologicalSpace X] {α : Type*} [TopologicalSpace α]
    [PreconnectedSpace α] (f : α → X) (hf : Continuous f)
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hsub : Set.range f ⊆ A ∪ B) {a₀ a₁ : α} (h₀ : f a₀ ∈ A) :
    f a₁ ∉ B :=
  fun hb => (Set.disjoint_left.mp hAB (path_confined_to_open f hf hA hB hAB hsub h₀ a₁)) hb

/-- **Lift confinement along the unit interval.** A continuous path `φ : I → X` (the lift of a loop
along the root covering) whose range lies in two disjoint opens `A ∪ B`, with `φ(0) ∈ A`, ends in `A`,
never reaching `B`. This is the literal statement used in the thesis (Theorem 4.2.2 proof): the lift
`φ''` of the deformed loop `Γ''`, with `φ''(0) = α ∈ D₁`, satisfies `φ''(1) ∉ D₂`. -/
theorem liftPath_confined {X : Type*} [TopologicalSpace X] (φ : unitInterval → X)
    (hφ : Continuous φ) {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hsub : ∀ t, φ t ∈ A ∪ B) (h₀ : φ 0 ∈ A) :
    φ 1 ∉ B :=
  path_endpoint_not_in_other φ hφ hA hB hAB
    (Set.range_subset_iff.mpr hsub) h₀

/-- **Loop-deformation contradiction** (the logical core of the homotopy argument, Theorem 4.2.2).

Suppose a covering map `p : E → X`, a base loop `γ` whose lift from `e` ends at a *different* fiber
point `e_β` (the root exchange `Γ_h[α] = β` supplied by Lemma 4.2.5), and a loop `γ''` to which `γ`
deforms (`HomotopicRel {0,1}`) whose lift from `e` stays inside one of two disjoint opens `A ∪ B` with
`e ∈ A` and `e_β ∈ B`. This is contradictory: by homotopy-invariance of lifted endpoints
(`liftPath_apply_one_eq_of_homotopicRel`) the lift of `γ''` also ends at `e_β ∈ B`, yet by confinement
(`liftPath_confined`) it ends in `A`, disjoint from `B`.

This isolates exactly what the geometric deformation of the thesis must produce: the homotopy `γ ≃ γ''`
and the confinement of `γ''`'s lift to the disc components. Both `Lemma 4.2.5` (the exchange) and the
explicit deformation are the remaining inputs. -/
theorem monodromy_exchange_contradiction {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p)
    {γ γ'' : C(unitInterval, X)} {e e_β : E}
    (he : γ 0 = p e) (he'' : γ'' 0 = p e)
    (hexch : cov.liftPath γ e he 1 = e_β)
    (hhom : γ.HomotopicRel γ'' {0, 1})
    {A B : Set E} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hconf : ∀ t, cov.liftPath γ'' e he'' t ∈ A ∪ B)
    (heA : e ∈ A) (heβB : e_β ∈ B) :
    False := by
  -- the lift of `γ''` ends where the lift of `γ` does — at `e_β` (homotopy invariance)
  have hend : cov.liftPath γ'' e he'' 1 = e_β :=
    (cov.liftPath_apply_one_eq_of_homotopicRel hhom e he he'').symm.trans hexch
  -- but the lift of `γ''` is confined to `A`, so its endpoint avoids `B`
  have hnotB : cov.liftPath γ'' e he'' 1 ∉ B :=
    liftPath_confined (cov.liftPath γ'' e he'') (cov.liftPath γ'' e he'').continuous
      hA hB hAB hconf (by rw [cov.liftPath_zero]; exact heA)
  exact hnotB (hend ▸ heβB)

end
