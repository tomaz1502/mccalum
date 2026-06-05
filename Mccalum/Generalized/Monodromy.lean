import Mccalum.Generalized.ComplexCovering
import Mccalum.Puiseux.Covering
import Mccalum.Puiseux.RootCover
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy reduction toward `irreducible_section_single_root_deg` (M0/M4)

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
`liftPath_confined`, `monodromy_exchange_contradiction`).

**Reactivation note (M0).** This file was archived in favour of the Newton–Puiseux route and is now
brought back into the build: the connectedness kernel of Lemma 4.2.5 — the missing
"Bochner–Martin content" — is supplied by `clopen_split_contradiction'`
(`Mccalum.Puiseux.RootCover`), so the monodromy route is unblocked (see `MONODROMY_PLAN.md`). The
topological half of Lemma 4.2.5, `transitive_monodromy_of_pathConnected`, now lives in
`Mccalum.Puiseux.Covering` (imported above) rather than being duplicated here. Remaining pieces:
M1 (path-connectedness from the clopen kernel), M2 (Rouché disc separation), M3 (the two explicit
deformations `Γ → Γ''`).
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

/-! ### Transitive monodromy from path-connectedness (the topological half of Lemma 4.2.5)

Lemma 4.2.5 (transitive monodromy: any two roots over `U` are connected by a path `Γ` with
`Γ_h[α] = α'`) splits into a *topological* half and an *algebraic* kernel:

* **topological half** `transitive_monodromy_of_pathConnected` (proved, now in
  `Mccalum.Puiseux.Covering`): if the total space `E` of the covering is path-connected, monodromy is
  transitive;
* **algebraic kernel**: the root variety of an *irreducible* Weierstrass polynomial is path-connected
  over `U` — the genuine Bochner–Martin [BMA48] content. This is no longer an isolated axiom: it is
  supplied by `clopen_split_contradiction'` (`Mccalum.Puiseux.RootCover`) via the
  preconnected ⟹ path-connected bridge (task **M1**). -/

open Polynomial Filter
open scoped Topology

/-- **A local homeomorphism pulls back local path-connectedness.** If `p : E → X` is a local
homeomorphism and `X` is locally path-connected, so is `E`. (Each point lies in a chart homeomorphic
to an open subset of `X`; pull back `X`'s path-connected neighbourhood basis through the chart's
inverse.) This fills a gap in Mathlib's covering API and gives `LocPathConnectedSpace` of a covering
total space over a locally path-connected base. -/
theorem IsLocalHomeomorph.locPathConnectedSpace {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (hp : IsLocalHomeomorph p) [LocPathConnectedSpace X] :
    LocPathConnectedSpace E := by
  refine LocPathConnectedSpace.of_bases
    (p := fun x V => V ∈ 𝓝 (p x) ∧ IsPathConnected V ∧ V ⊆ (hp x).choose.target)
    (s := fun x V => (hp x).choose.symm '' V) (fun x => ?_) (fun x V hV => ?_)
  · set e := (hp x).choose with he
    have hxe : x ∈ e.source := (hp x).choose_spec.1
    have hpx : p x = e x := congrFun (hp x).choose_spec.2 x
    have hex : e x ∈ e.target := e.map_source hxe
    have hmap := (pathConnected_subset_basis e.open_target hex).map e.symm
    rw [e.symm_map_nhds_eq hxe] at hmap
    simpa only [hpx] using hmap
  · set e := (hp x).choose with he
    exact hV.2.1.image' (e.continuousOn_symm.mono (e.symm_source ▸ hV.2.2))

open Classical in
/-- **M1a, count step.** For a set `W` of the root variety that is clopen over the punctured separable
base `U` and contains a sheet `e` lying over a point of `U`, the number of `W`-roots is `≥ 1`
frequently near `0`. (The count is locally constant on the connected `U` and positive at `e`'s base
point, hence positive throughout `U ∈ 𝓝[≠]0`.) -/
private theorem rootCover_count_pos_freq {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {W : Set ↥(rootVariety q)} (hW : IsClopenOverBase q U W)
    {e : ↥(rootVariety q)} (heU : (e : (Fin 1 → ℂ) × ℂ).1 ∈ U) (heW : e ∈ W) :
    ∃ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      1 ≤ ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' W))).card := by
  classical
  set cnt : (Fin 1 → ℂ) → ℕ := fun y =>
    ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' W))).card with hcnt
  haveI : PreconnectedSpace (↥U) := Subtype.preconnectedSpace hUconn
  have hlc : IsLocallyConstant (fun v : ↥U => cnt v.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hev := aRootCount_eventually_eq q hmonic hdeg (fun i => hcoeff i v.1) (hUsep v.1 v.2)
      hUopen v.2 (A := W) hW
    exact (continuous_subtype_val.continuousAt).eventually hev
  have hcnt_e : 1 ≤ cnt (e : (Fin 1 → ℂ) × ℂ).1 := by
    rw [hcnt]
    apply Finset.card_pos.mpr
    refine ⟨(e : (Fin 1 → ℂ) × ℂ).2, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic _).ne_zero]
      exact e.2
    · exact ⟨e, heW, rfl⟩
  refine Filter.Eventually.frequently ?_
  filter_upwards [hU0] with y hy
  have hconst : cnt y = cnt (e : (Fin 1 → ℂ) × ℂ).1 :=
    hlc.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨_, heU⟩
  show 1 ≤ cnt y
  rw [hconst]; exact hcnt_e

open Classical in
/-- **M1a.** For an irreducible univariate Weierstrass family, the root cover over a punctured
separable, preconnected base `U ∈ 𝓝[≠] 0` is **preconnected**: any clopen split would give two
nonempty components, hence two positive `∃ᶠ` counts, contradicting the (now non-vacuous) kernel
`clopen_split_contradiction'`. This is the connectedness half of Lemma 4.2.5. -/
theorem rootCover_preconnected {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducible q)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε) :
    PreconnectedSpace ↥(rootProj q ⁻¹' U) := by
  classical
  have hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable := by
    filter_upwards [hU0] with y hy using hUsep y hy
  rw [preconnectedSpace_iff_clopen]
  intro A hAcl
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hAne_empty, hAne_univ⟩ := hcon
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hAne_empty
  obtain ⟨b, hb⟩ : (Aᶜ).Nonempty := Set.nonempty_compl.mpr hAne_univ
  set Arv : Set ↥(rootVariety q) := Subtype.val '' A with hArv
  have hArv_base : IsClopenOverBase q U Arv := by
    show IsClopen (Subtype.val ⁻¹' Arv : Set ↥(rootProj q ⁻¹' U))
    rw [hArv, Set.preimage_image_eq A Subtype.val_injective]
    exact hAcl
  have hAfreq := rootCover_count_pos_freq q hmonic hdeg hcoeff hUopen hUconn hUsep hU0
    hArv_base (e := a.1) a.2 ⟨a, ha, rfl⟩
  have hBfreq := rootCover_count_pos_freq q hmonic hdeg hcoeff hUopen hUconn hUsep hU0
    hArv_base.compl (e := b.1) b.2 (by
      intro hmem
      obtain ⟨x, hx, hxb⟩ := hmem
      exact hb (Subtype.ext hxb ▸ hx))
  exact clopen_split_contradiction' q hmonic hdeg hcoeff hq0 hsep hε hbdd hirr hUopen hUconn hUsep hU0
    hArv_base hAfreq hBfreq

/-- **M1b.** For an irreducible univariate Weierstrass family of positive degree, the root cover over a
punctured separable, preconnected base `U ∈ 𝓝[≠] 0` is **path-connected**. Combines `rootCover_preconnected`
(M1a) with local path-connectedness of the cover (the covering map is a local homeomorphism over the
open base `U ⊆ ℂ`) and nonemptiness (`q y` has a root for `y ∈ U`). -/
theorem rootCover_pathConnected {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducible q)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε) :
    PathConnectedSpace ↥(rootProj q ⁻¹' U) := by
  have hcont : ∀ i, Continuous (fun y => (q y).coeff i) :=
    fun i => continuous_iff_continuousAt.mpr fun y => (hcoeff i y).continuousAt
  have cov : IsCoveringMap (U.restrictPreimage (rootProj q)) :=
    rootProj_isCoveringMap_restrict q hmonic hdeg hcont U (fun i y _ => hcoeff i y) hUsep
  haveI : LocPathConnectedSpace ↥U := hUopen.locPathConnectedSpace
  haveI : LocPathConnectedSpace ↥(rootProj q ⁻¹' U) := cov.isLocalHomeomorph.locPathConnectedSpace
  haveI : PreconnectedSpace ↥(rootProj q ⁻¹' U) :=
    rootCover_preconnected q hmonic hdeg hcoeff hq0 hirr hUopen hUconn hUsep hU0 hε hbdd
  haveI : Nonempty ↥(rootProj q ⁻¹' U) := by
    obtain ⟨y₀, hy₀⟩ := Filter.nonempty_of_mem hU0
    obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (q y₀) (by
      rw [Polynomial.degree_eq_natDegree (hmonic y₀).ne_zero, hdeg y₀]
      exact_mod_cast hm.ne')
    exact ⟨⟨⟨(y₀, t₀), ht₀⟩, hy₀⟩⟩
  haveI : ConnectedSpace ↥(rootProj q ⁻¹' U) := ⟨inferInstance⟩
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- The root cover over a base `U` on which `q` is separable is a covering map (the analytic IFT
trivializations of `ComplexCovering`, packaged for the punctured base). -/
theorem rootCover_isCoveringMap {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {U : Set (Fin 1 → ℂ)} (hUsep : ∀ y ∈ U, (q y).Separable) :
    IsCoveringMap (U.restrictPreimage (rootProj q)) :=
  rootProj_isCoveringMap_restrict q hmonic hdeg
    (fun i => continuous_iff_continuousAt.mpr fun y => (hcoeff i y).continuousAt) U
    (fun i y _ => hcoeff i y) hUsep

/-- **M1c — Lemma 4.2.5 (root exchange / transitive monodromy).** For an irreducible univariate
Weierstrass family, any two sheets `e₀, e₁` of the root cover over the same base point of `U` are
joined by a base loop `γ` whose lift from `e₀` ends at `e₁`. This is the full transitive-monodromy
input to the homotopy-deformation contradiction (the thesis's `Γ_h[α] = β`), assembled from
path-connectedness of the cover (M1b) and `transitive_monodromy_of_pathConnected`. -/
theorem rootCover_exchange {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducible q)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    {e₀ e₁ : ↥(rootProj q ⁻¹' U)}
    (hpe : U.restrictPreimage (rootProj q) e₀ = U.restrictPreimage (rootProj q) e₁) :
    ∃ (γ : C(unitInterval, ↥U)) (hγ0 : γ 0 = U.restrictPreimage (rootProj q) e₀),
      γ 1 = U.restrictPreimage (rootProj q) e₀ ∧
        (rootCover_isCoveringMap q hmonic hdeg hcoeff hUsep).liftPath γ e₀ hγ0 1 = e₁ := by
  haveI : PathConnectedSpace ↥(rootProj q ⁻¹' U) :=
    rootCover_pathConnected q hm hmonic hdeg hcoeff hq0 hirr hUopen hUconn hUsep hU0 hε hbdd
  exact transitive_monodromy_of_pathConnected
    (rootCover_isCoveringMap q hmonic hdeg hcoeff hUsep) hpe

end


