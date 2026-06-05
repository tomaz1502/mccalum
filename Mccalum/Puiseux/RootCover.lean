import Mccalum.Generalized.ComplexCovering
import Mccalum.Puiseux.RootFactor
import Mccalum.Puiseux.Connectedness

/-!
# C4.3 instantiation — local root sections enumerate the fibre

This file connects the reactivated analytic covering infrastructure (`local_disjoint_root_sections`,
`separable_distinct_simple_roots`, `evalFamily_analyticAt`, `evalFamily_fderiv_t`) to the abstract
gluing lemma `globalPartialProd_analyticAt`: at a point `y₀` where the family `q` is separable, there
is a neighbourhood `V` on which `d` analytic sections `φ i` enumerate the roots of `q y` (distinctly).
This discharges the `hroots`/`hinj`/`hφ` hypotheses of the global factor's analyticity.
-/

open Polynomial

/-- **Clopen-over-a-subspace constancy.** Variant of `clopen_mem_const_of_continuous` where `A` is only
required to be clopen in a *subspace* `C` containing the whole range of the continuous map `s`. This is
what makes the connectedness arguments non-vacuous over the **branched** root variety: we take `C` to be
the cover over the separable locus (which excludes the branch points), where nontrivial clopens exist —
a clopen of the full `rootVariety` containing a branch point must contain every colliding sheet, which
would force one side of any split to be empty. -/
theorem clopen_mem_const_over_sub {E V' : Type*} [TopologicalSpace E] [TopologicalSpace V']
    [PreconnectedSpace V'] {s : V' → E} (hs : Continuous s) {C : Set E} (hsC : ∀ v, s v ∈ C)
    {A : Set E} (hA : IsClopen (Subtype.val ⁻¹' A : Set ↥C)) {v₀ v₁ : V'} (hmem : s v₀ ∈ A) :
    s v₁ ∈ A :=
  clopen_mem_const_of_continuous (s := fun v => (⟨s v, hsC v⟩ : ↥C)) (hs.subtype_mk hsC) hA
    (v₀ := v₀) (v₁ := v₁) hmem

/-- **`A` is clopen over the base `U`**: its restriction to the cover `rootProj⁻¹ U` (which excludes the
branch points when `q` is separable on `U`) is clopen. This is the non-vacuous replacement for
`IsClopen A` on the full branched `rootVariety`: over the punctured base the sheets no longer collide,
so genuine splittings exist and the count conditions `1 ≤ d_A`, `1 ≤ d_B` become satisfiable. -/
def IsClopenOverBase {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (U : Set (Fin n → ℂ))
    (A : Set ↥(rootVariety q)) : Prop :=
  IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U))

theorem IsClopenOverBase.compl {n : ℕ} {q : (Fin n → ℂ) → Polynomial ℂ} {U : Set (Fin n → ℂ)}
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) : IsClopenOverBase q U Aᶜ := by
  unfold IsClopenOverBase at hA ⊢
  rw [Set.preimage_compl]
  exact hA.compl

/-- **Local analytic root sections enumerating the fibre.** At a separable point `y₀` of a monic
degree-`d` analytic family `q`, there is an open neighbourhood `V ∋ y₀` and analytic sections
`φ : Fin d → (Fin n → ℂ) → ℂ` such that for every `y ∈ V`, the values `φ i y` are *distinct* and form
*exactly* the root set of `q y`. -/
theorem exists_local_root_sections {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    (B : Set (Fin n → ℂ)) (hBopen : IsOpen B) (hy₀B : y₀ ∈ B) :
    ∃ (V : Set (Fin n → ℂ)) (φ : Fin d → (Fin n → ℂ) → ℂ),
      IsOpen V ∧ y₀ ∈ V ∧ IsPreconnected V ∧ V ⊆ B ∧
      (∀ i, AnalyticOn ℂ (φ i) V) ∧
      (∀ y ∈ V, Function.Injective (fun i => φ i y)) ∧
      (∀ y ∈ V, (q y).roots.toFinset = Finset.univ.image (fun i => φ i y)) := by
  classical
  -- the `d` distinct simple roots of `q y₀`
  obtain ⟨t, ht_inj, ht_roots, ht_simple⟩ :=
    separable_distinct_simple_roots (q y₀) d (hmonic y₀) (hdeg y₀) hsep
  set F : (Fin n → ℂ) × ℂ → ℂ := fun p => (q p.1).eval p.2 with hF
  have hroot : ∀ j, F (y₀, t j) = 0 := fun j => (ht_roots (t j)).mpr ⟨j, rfl⟩
  have hF_an : ∀ j, AnalyticAt ℂ F (y₀, t j) :=
    fun j => evalFamily_analyticAt q hdeg (t j) hcoeff
  have hsimple : ∀ j, fderiv ℂ F (y₀, t j) (0, 1) ≠ 0 := by
    intro j
    rw [evalFamily_fderiv_t q hdeg (t j) hcoeff]
    exact ht_simple j
  obtain ⟨U, φ, hUopen, hy₀U, hφan, _hφval, hφroot, hφdisj⟩ :=
    local_disjoint_root_sections F y₀ d t ht_inj hF_an hroot hsimple
  -- shrink `U ∩ B` to an open ball `V ⊆ U ∩ B` around `y₀` (preconnected, inside the base `B`)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hUopen.inter hBopen) y₀ ⟨hy₀U, hy₀B⟩
  have hballU : Metric.ball y₀ r ⊆ U := fun x hx => (hball hx).1
  refine ⟨Metric.ball y₀ r, φ, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball y₀ r).isPreconnected, fun x hx => (hball hx).2,
    fun i => (hφan i).mono hballU, ?_, ?_⟩
  · intro y hy i j hij
    by_contra hne
    exact hφdisj i j hne y (hballU hy) hij
  · intro y hy
    refine roots_toFinset_eq_image_of_monic (hmonic y) (hdeg y) (fun i => φ i y) ?_ ?_
    · intro i j hij
      by_contra hne
      exact hφdisj i j hne y (hballU hy) hij
    · intro i
      have := hφroot i y (hballU hy)
      rwa [hF] at this

open scoped Topology in
open Classical in
/-- **The Weierstrass factor of a clopen component is analytic on the separable locus.** For a clopen
component `A` of the root variety, the partial product over the roots of `q y` lying in `A` (`h_A`) has
analytic coefficients at every separable point `y₀`. Combines `exists_local_root_sections` (sections
enumerate the roots), `clopen_mem_const_of_continuous` (component membership is locally constant along
sheets — single-valuedness), and `globalPartialProd_analyticAt` (the gluing). -/
theorem factor_coeff_analyticAt {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    {U : Set (Fin n → ℂ)} (hUopen : IsOpen U) (hy₀U : y₀ ∈ U)
    (A : Set ↥(rootVariety q)) (hA : IsClopenOverBase q U A) (j : ℕ) :
    AnalyticAt ℂ (fun y => ((q y).roots.toFinset.filter
        (fun t => (y, t) ∈ (Subtype.val '' A))).prod
        (fun t => X - C t) |>.coeff j) y₀ := by
  classical
  have hA' : IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U)) := hA
  obtain ⟨V, φ, hVopen, hy₀V, hVconn, hVU, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep U hUopen hy₀U
  have hVnhds : V ∈ 𝓝 y₀ := hVopen.mem_nhds hy₀V
  have hroot : ∀ i, ∀ y, y ∈ V → (q y).eval (φ i y) = 0 := by
    intro i y hy
    have hmem : φ i y ∈ (q y).roots.toFinset := by
      rw [hφroots y hy]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at hmem
    exact hmem
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  let P : (Fin n → ℂ) → ℂ → Prop := fun y t => (y, t) ∈ (Subtype.val '' A)
  have hconst : ∀ i, ∀ y ∈ V, (P y (φ i y) ↔ P y₀ (φ i y₀)) := by
    intro i y hy
    set σ : V → ↥(rootVariety q) := fun v => ⟨(v.1, φ i v.1), hroot i v.1 v.2⟩ with hσ
    have hσcont : Continuous σ :=
      (continuous_subtype_val.prodMk ((hφan i).continuousOn.restrict)).subtype_mk
        (fun v => hroot i v.1 v.2)
    have hsC : ∀ v : V, σ v ∈ rootProj q ⁻¹' U := fun v => hVU v.2
    have hPσ : ∀ z (hz : z ∈ V), (P z (φ i z) ↔ σ ⟨z, hz⟩ ∈ A) := by
      intro z hz
      constructor
      · rintro ⟨a, ha, hav⟩
        have heq : a = σ ⟨z, hz⟩ := Subtype.ext hav
        rwa [heq] at ha
      · intro hmem; exact ⟨σ ⟨z, hz⟩, hmem, rfl⟩
    rw [hPσ y hy, hPσ y₀ hy₀V]
    exact ⟨fun h => clopen_mem_const_over_sub hσcont hsC hA' h,
      fun h => clopen_mem_const_over_sub hσcont hsC hA' h⟩
  have hφan₀ : ∀ i, AnalyticAt ℂ (φ i) y₀ := fun i => (hφan i).analyticAt hVnhds
  exact globalPartialProd_analyticAt q φ P hVnhds hφroots hφinj hconst hφan₀ j

open scoped Topology in
open Classical in
/-- **The factor `h_A`'s coefficient extends analytically across the discriminant point `0`.** For a
clopen component `A`, the coefficient of the partial product `h_A` — analytic on the punctured
(separable) neighbourhood of `0` (`factor_coeff_analyticAt`) and bounded there (`norm_coeff_factor_le`,
from the root bound) — extends to a function analytic *at* `0` agreeing with it off `0`. Combines the
separable-locus analyticity, the uniform bound, and the removable-singularity transport
`exists_analyticAt_extend_funUnique`. -/
theorem factor_coeff_extends {d : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    (A : Set ↥(rootVariety q)) (hA : IsClopenOverBase q U A) (j : ℕ) :
    ∃ F : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ F 0 ∧
      F =ᶠ[𝓝[≠] (0 : Fin 1 → ℂ)]
        (fun y => ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).prod
          (fun t => X - C t) |>.coeff j) := by
  refine exists_analyticAt_extend_funUnique ?_ (M := (1 + ε) ^ d) ?_
  · filter_upwards [hsep, hU0] with y hy hyU
    exact factor_coeff_analyticAt q hmonic hdeg (fun i => hcoeff i y) hy hUopen hyU A hA j
  · filter_upwards [hbdd] with y hy
    have hbound := norm_coeff_factor_le hε (fun t => (y, t) ∈ (Subtype.val '' A)) hy j
    rwa [hdeg y] at hbound

/-- **The factorisation `q = h_A · h_B` on the separable locus.** At a separable point the family value
splits as the product over the `P`-roots times the product over the `¬P`-roots — the algebraic identity
that, propagated across `0` by the identity theorem, yields the Weierstrass factorisation contradicting
irreducibility. -/
theorem family_eq_factor_mul {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) {y : Fin n → ℂ} (hsep : (q y).Separable)
    (P : ℂ → Prop) [DecidablePred P] :
    q y = ((q y).roots.toFinset.filter P).prod (fun t => X - C t)
        * ((q y).roots.toFinset.filter (fun t => ¬ P t)).prod (fun t => X - C t) :=
  eq_prod_filter_mul_prod_filter_not_of_monic_separable (hmonic y) hsep P

open Classical in
/-- **Component membership of a sheet is locally constant.** Along a continuous root branch `φ` over a
preconnected `V`, membership of the sheet `(y, φ y)` in a clopen component `A` does not vary. This is
the single-section single-valuedness core, extracted for reuse in both `factor_coeff_analyticAt` (the
factor's coefficients) and `aRootCount_eventually_eq` (the factor's degree). -/
theorem sheet_mem_locally_const {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {V : Set (Fin n → ℂ)} (hVconn : IsPreconnected V) {φ : (Fin n → ℂ) → ℂ}
    (hφroot : ∀ y ∈ V, (q y).eval (φ y) = 0) (hφcont : ContinuousOn φ V)
    {U : Set (Fin n → ℂ)} (hVU : V ⊆ U)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A)
    {y₀ y : Fin n → ℂ} (hy₀ : y₀ ∈ V) (hy : y ∈ V) :
    ((y, φ y) ∈ (Subtype.val '' A) ↔ (y₀, φ y₀) ∈ (Subtype.val '' A)) := by
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  have hA' : IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U)) := hA
  set σ : V → ↥(rootVariety q) := fun v => ⟨(v.1, φ v.1), hφroot v.1 v.2⟩ with hσ
  have hσcont : Continuous σ :=
    (continuous_subtype_val.prodMk (hφcont.restrict)).subtype_mk (fun v => hφroot v.1 v.2)
  have hsC : ∀ v : V, σ v ∈ rootProj q ⁻¹' U := fun v => hVU v.2
  have hPσ : ∀ z (hz : z ∈ V), ((z, φ z) ∈ (Subtype.val '' A) ↔ σ ⟨z, hz⟩ ∈ A) := by
    intro z hz
    constructor
    · rintro ⟨a, ha, hav⟩
      have heq : a = σ ⟨z, hz⟩ := Subtype.ext hav
      rwa [heq] at ha
    · intro hmem; exact ⟨σ ⟨z, hz⟩, hmem, rfl⟩
  rw [hPσ y hy, hPσ y₀ hy₀]
  exact ⟨fun h => clopen_mem_const_over_sub hσcont hsC hA' h,
    fun h => clopen_mem_const_over_sub hσcont hsC hA' h⟩

open scoped Topology in
open Classical in
/-- **The `A`-root count is locally constant.** Near a separable point `y₀`, the number of roots of
`q y` lying in a clopen component `A` is constant. (The roots are the distinct section values, and
component membership is locally constant by `sheet_mem_locally_const`.) Propagated over the connected
punctured disc, this gives the constant degree `d_A` of the Weierstrass factor `h_A`. -/
theorem aRootCount_eventually_eq {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    {U : Set (Fin n → ℂ)} (hUopen : IsOpen U) (hy₀U : y₀ ∈ U)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) :
    ∀ᶠ y in 𝓝 y₀, ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card
        = ((q y₀).roots.toFinset.filter (fun t => (y₀, t) ∈ (Subtype.val '' A))).card := by
  obtain ⟨V, φ, hVopen, hy₀V, hVconn, hVU, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep U hUopen hy₀U
  have hroot : ∀ i, ∀ y ∈ V, (q y).eval (φ i y) = 0 := by
    intro i y hy
    have hmem : φ i y ∈ (q y).roots.toFinset := by
      rw [hφroots y hy]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at hmem
    exact hmem
  have key : ∀ z ∈ V, ((q z).roots.toFinset.filter (fun t => (z, t) ∈ (Subtype.val '' A))).card
      = (Finset.univ.filter (fun i => (z, φ i z) ∈ (Subtype.val '' A))).card := by
    intro z hz
    rw [hφroots z hz, Finset.filter_image, Finset.card_image_of_injective _ (hφinj z hz)]
  filter_upwards [hVopen.mem_nhds hy₀V] with y hy
  rw [key y hy, key y₀ hy₀V]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact sheet_mem_locally_const q hVconn (hroot i) ((hφan i).continuousOn) hVU hA hy₀V hy

open scoped Topology in
open Classical in
/-- **The `A`-root count is globally constant on the punctured disc.** Given that a punctured
neighbourhood of `0` is separable (`0` an isolated discriminant zero), the number `d_A` of roots in a
clopen component `A` is the same for all `y` near `0` (excluding `0`). The count is locally constant
(`aRootCount_eventually_eq`) on the *connected* punctured disc (`isPathConnected_ball_diff_singleton`),
hence globally constant — this is the well-defined degree of the Weierstrass factor `h_A`. -/
theorem aRootCount_eventually_const {d : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) :
    ∃ dA : ℕ, ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card = dA := by
  set cnt : (Fin 1 → ℂ) → ℕ := fun y =>
    ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card with hcnt
  haveI : PreconnectedSpace (↥U) := Subtype.preconnectedSpace hUconn
  have hlc : IsLocallyConstant (fun v : ↥U => cnt v.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hev := aRootCount_eventually_eq q hmonic hdeg (fun i => hcoeff i v.1) (hUsep v.1 v.2) hUopen
      v.2 (A := A) hA
    exact (continuous_subtype_val.continuousAt).eventually hev
  obtain ⟨y₁, hy₁⟩ := Filter.nonempty_of_mem hU0
  refine ⟨cnt y₁, ?_⟩
  filter_upwards [hU0] with y hy
  exact hlc.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨y₁, hy₁⟩

open scoped Topology in
open Classical in
/-- **The Weierstrass factor `H_A` of a clopen component.** From the analytic extensions of `h_A`'s
coefficients (`factor_coeff_extends`) and the constant degree `d_A` (`aRootCount_eventually_const`),
build `H_A := X ^ d_A + ∑_{j < d_A} C (F_j ·) X^j`: a family that is monic of degree `d_A` everywhere,
has analytic coefficients at `0`, and agrees with the partial product `h_A` off `0`. (The Weierstrass
`coeff_zero_vanish`, `H_A 0 = X ^ d_A`, follows later from the factorization `q = H_A · H_B`.) -/
theorem exists_factor_weierstrass {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA : ℕ} (hdA : 1 ≤ dA)
    (hdA_eq : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card = dA) :
    ∃ HA : (Fin 1 → ℂ) → Polynomial ℂ,
      (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧
      HA =ᶠ[𝓝[≠] (0 : Fin 1 → ℂ)]
        (fun y => ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).prod
          (fun t => X - C t)) := by
  set hpA : (Fin 1 → ℂ) → Polynomial ℂ :=
    fun y => ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).prod
      (fun t => X - C t) with hhpA
  choose Fj hFj_an hFj_eq using fun j =>
    factor_coeff_extends q hmonic hdeg hcoeff hsep hε hbdd hUopen hU0 A hA j
  set HA : (Fin 1 → ℂ) → Polynomial ℂ :=
    fun y => X ^ dA + ∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j with hHA
  have hlower_deg : ∀ y, (∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j).natDegree < dA := by
    intro y
    rcases eq_or_ne (∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j) 0 with h0 | hne
    · rw [h0, Polynomial.natDegree_zero]; omega
    · rw [Polynomial.natDegree_lt_iff_degree_lt hne]; exact degree_sum_C_mul_X_pow_lt _
  have hmono : ∀ y, (HA y).Monic := by
    intro y; simp only [hHA]; exact (monic_natDegree_X_pow_add (hlower_deg y)).1
  have hdeg_HA : ∀ y, (HA y).natDegree = dA := by
    intro y; simp only [hHA]; exact (monic_natDegree_X_pow_add (hlower_deg y)).2
  have hHA_coeff : ∀ y i, (HA y).coeff i
      = (if i = dA then 1 else 0) + (if i < dA then Fj i y else 0) := by
    intro y i
    rw [hHA]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range dA) i (fun j => Fj j y)]
    simp only [Finset.mem_range]
  have han : ∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0 := by
    intro i
    have heqf : (fun y => (HA y).coeff i)
        = (fun y => (if i = dA then 1 else 0) + (if i < dA then Fj i y else 0)) := by
      funext y; exact hHA_coeff y i
    rw [heqf]
    apply AnalyticAt.add analyticAt_const
    by_cases hi : i < dA
    · simp only [if_pos hi]; exact hFj_an i
    · simp only [if_neg hi]; exact analyticAt_const
  refine ⟨HA, hmono, hdeg_HA, han, ?_⟩
  have hall : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ j ∈ Finset.range dA, Fj j y = (hpA y).coeff j :=
    (Finset.eventually_all (Finset.range dA)).mpr (fun j _ => hFj_eq j)
  filter_upwards [hall, hdA_eq] with y hyall hycount
  show X ^ dA + ∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j = hpA y
  rw [Finset.sum_congr rfl (fun j hj => by rw [hyall j hj])]
  have hmono_hpA : (hpA y).Monic := by rw [hhpA]; exact monic_prod_X_sub_C _
  have hdeg_hpA : (hpA y).natDegree = dA := by
    rw [hhpA, natDegree_prod_X_sub_C]; exact hycount
  exact (monic_eq_X_pow_add_lower hmono_hpA hdeg_hpA).symm

/-- **`Aᶜ`-membership equals non-`A`-membership on the root variety.** For a root `t` of `q y` (so
`(y, t)` is a genuine sheet), the sheet lies in the complementary component `Aᶜ` iff it does not lie in
`A`. This identifies the `B = Aᶜ` partial product (`h_{Aᶜ}`) with the `¬A` factor of
`family_eq_factor_mul`. -/
theorem mem_image_compl_iff_not_mem_image {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {A : Set ↥(rootVariety q)} {y : Fin n → ℂ} {t : ℂ} (ht : (q y).eval t = 0) :
    ((y, t) ∈ (Subtype.val '' Aᶜ)) ↔ ¬ ((y, t) ∈ (Subtype.val '' A)) := by
  have hmem : ((y, t) : (Fin n → ℂ) × ℂ) ∈ rootVariety q := ht
  constructor
  · rintro ⟨a, ha, hav⟩ hAmem
    obtain ⟨b, hb, hbv⟩ := hAmem
    have hab : a = b := Subtype.ext (hav.trans hbv.symm)
    rw [hab] at ha
    exact ha hb
  · intro hnA
    exact ⟨⟨(y, t), hmem⟩, fun hb => hnA ⟨⟨(y, t), hmem⟩, hb, rfl⟩, rfl⟩

open Classical in
/-- The `Aᶜ`-partial product equals the `¬A` factor of `family_eq_factor_mul`. -/
theorem factor_compl_eq {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (hmonic : ∀ y, (q y).Monic)
    {A : Set ↥(rootVariety q)} (y : Fin n → ℂ) :
    ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' Aᶜ))).prod (fun t => X - C t)
      = ((q y).roots.toFinset.filter
          (fun t => ¬ ((y, t) ∈ (Subtype.val '' A)))).prod (fun t => X - C t) :=
  Finset.prod_congr (Finset.filter_congr (fun t ht => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at ht
    exact mem_image_compl_iff_not_mem_image q ht)) (fun _ _ => rfl)

open scoped Topology in
open Classical in
/-- **A clopen split yields a Weierstrass factorisation `q = H_A · H_B`.** Given a clopen component `A`
of the root variety (with both `A` and `Aᶜ` contributing a positive number of sheets, `1 ≤ d_A`,
`1 ≤ d_B`), the family `q` factors near `0` as a product of two monic, analytic-coefficient families of
positive degrees `d_A`, `d_B`, each equal to a power of `X` at `0`. This is the heart of the
nonsplitting/connectedness proof: such a factorisation contradicts irreducibility. (Wiring this to the
project's `CParam`-based `WeierstrassIrreducible` is task C4.2.) -/
theorem clopen_split_factorization {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m)
    (hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA dB : ℕ}
    (hdA : 1 ≤ dA) (hdB : 1 ≤ dB)
    (hdA_eq : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card = dA)
    (hdB_eq : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' Aᶜ))).card = dB) :
    ∃ HA HB : (Fin 1 → ℂ) → Polynomial ℂ,
      (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧ HA 0 = X ^ dA ∧
      (∀ y, (HB y).Monic) ∧ (∀ y, (HB y).natDegree = dB) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HB y).coeff i) 0) ∧ HB 0 = X ^ dB ∧
      (∀ᶠ y in 𝓝 (0 : Fin 1 → ℂ), q y = HA y * HB y) := by
  obtain ⟨HA, hHA_mono, hHA_deg, hHA_an, hHA_eq⟩ :=
    exists_factor_weierstrass q hmonic hdeg hcoeff hsep hε hbdd hUopen hU0 hA hdA hdA_eq
  obtain ⟨HB, hHB_mono, hHB_deg, hHB_an, hHB_eq⟩ :=
    exists_factor_weierstrass q hmonic hdeg hcoeff hsep hε hbdd hUopen hU0 hA.compl hdB hdB_eq
  -- `q = H_A · H_B` off `0`
  have hoff : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), q y = HA y * HB y := by
    filter_upwards [hsep, hHA_eq, hHB_eq] with y hysep hyHA hyHB
    rw [hyHA, hyHB, factor_compl_eq q hmonic y]
    exact family_eq_factor_mul q hmonic hysep (fun t => (y, t) ∈ (Subtype.val '' A))
  -- product coefficients are analytic at `0`
  have hprod_an : ∀ k, AnalyticAt ℂ (fun y => (HA y * HB y).coeff k) 0 := by
    intro k
    have : (fun y => (HA y * HB y).coeff k)
        = fun y => ∑ p ∈ Finset.antidiagonal k, (HA y).coeff p.1 * (HB y).coeff p.2 := by
      funext y; rw [Polynomial.coeff_mul]
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun p _ => (hHA_an p.1).mul (hHB_an p.2)
  -- `q 0 = H_A 0 · H_B 0` by coefficient continuity
  have hval0 : q 0 = HA 0 * HB 0 :=
    polynomial_eq_of_eventuallyEq_punctured hoff
      (fun j => (hcoeff j 0).continuousAt) (fun j => (hprod_an j).continuousAt)
  -- `H_A 0 = X ^ d_A`, `H_B 0 = X ^ d_B`
  have hHA0 : HA 0 = X ^ dA := by
    have hdvd : HA 0 ∣ X ^ m := by rw [← hq0, hval0]; exact Dvd.intro _ rfl
    have := eq_X_pow_of_monic_dvd_X_pow (hHA_mono 0) hdvd
    rwa [hHA_deg 0] at this
  have hHB0 : HB 0 = X ^ dB := by
    have hdvd : HB 0 ∣ X ^ m := by rw [← hq0, hval0]; exact Dvd.intro_left _ rfl
    have := eq_X_pow_of_monic_dvd_X_pow (hHB_mono 0) hdvd
    rwa [hHB_deg 0] at this
  -- propagate `q = H_A · H_B` to a full neighbourhood of `0`
  have hnear : ∀ᶠ y in 𝓝 (0 : Fin 1 → ℂ), q y = HA y * HB y :=
    eventuallyEq_nhds_of_nhdsWithin_ne hoff hval0
  exact ⟨HA, HB, hHA_mono, hHA_deg, hHA_an, hHA0, hHB_mono, hHB_deg, hHB_an, hHB0, hnear⟩

open scoped Topology in
/-- **Univariate Weierstrass irreducibility.** A univariate family `q` over `Fin 1 → ℂ` admits no germ
factorization at `0` into two monic, analytic-coefficient families of positive degree (each a power of
`X` at `0`). This is the `Fin 1 → ℂ` analogue of `WeierstrassIrreducible`; relating it to the project's
`CParam`-based `WeierstrassIrreducible` is task C4.2. -/
def UnivIrreducible (q : (Fin 1 → ℂ) → Polynomial ℂ) : Prop :=
  ¬ ∃ (dA dB : ℕ) (HA HB : (Fin 1 → ℂ) → Polynomial ℂ),
    1 ≤ dA ∧ 1 ≤ dB ∧
    (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧ HA 0 = X ^ dA ∧
    (∀ y, (HB y).Monic) ∧ (∀ y, (HB y).natDegree = dB) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HB y).coeff i) 0) ∧ HB 0 = X ^ dB ∧
    (∀ᶠ y in 𝓝 (0 : Fin 1 → ℂ), q y = HA y * HB y)

open scoped Topology in
open Classical in
/-- **Irreducible ⟹ no nontrivial clopen split of the root cover (connectedness contrapositive).**
For an irreducible univariate Weierstrass family, no clopen component `A` of the root variety can have
*both* `A` and `Aᶜ` contributing a positive number of sheets near `0` — because such a split would
yield, via `clopen_split_factorization`, a Weierstrass factorization, contradicting irreducibility.
This is the connectedness statement of C4.3 over the `Fin 1 → ℂ` base: irreducibility forces the root
cover to be connected. (Discharging the `1 ≤ d_A`/`1 ≤ d_B` nontriviality from `A`/`Aᶜ` nonempty over
the punctured disc, and wiring to the `CParam` axiom, is task C4.2.) -/
theorem clopen_split_contradiction {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m)
    (hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    (hirr : UnivIrreducible q)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA dB : ℕ}
    (hdA : 1 ≤ dA) (hdB : 1 ≤ dB)
    (hdA_eq : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card = dA)
    (hdB_eq : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' Aᶜ))).card = dB) :
    False := by
  obtain ⟨HA, HB, hHA_mono, hHA_deg, hHA_an, hHA0, hHB_mono, hHB_deg, hHB_an, hHB0, hnear⟩ :=
    clopen_split_factorization q hmonic hdeg hcoeff hq0 hsep hε hbdd hUopen hU0 hA hdA hdB
      hdA_eq hdB_eq
  exact hirr ⟨dA, dB, HA, HB, hdA, hdB, hHA_mono, hHA_deg, hHA_an, hHA0,
    hHB_mono, hHB_deg, hHB_an, hHB0, hnear⟩

open scoped Topology in
open Classical in
/-- **Irreducible ⟹ root cover connected (self-contained form).** The count hypotheses are discharged
internally via `aRootCount_eventually_const`, and the positive-degree requirement is reduced to the
honest *nontriviality* of the split: both `A` and `Aᶜ` have a root over points arbitrarily close to `0`
(`∃ᶠ`). For an irreducible univariate Weierstrass family there is no such nontrivial clopen split —
i.e. the root cover near `0` is connected. -/
theorem clopen_split_contradiction' {m : ℕ} (q : (Fin 1 → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m)
    (hsep : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε)
    (hirr : UnivIrreducible q)
    {U : Set (Fin 1 → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ))
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A)
    (hAne : ∃ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      1 ≤ ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card)
    (hBne : ∃ᶠ y in 𝓝[≠] (0 : Fin 1 → ℂ),
      1 ≤ ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' Aᶜ))).card) :
    False := by
  obtain ⟨dA, hdA_eq⟩ := aRootCount_eventually_const q hmonic hdeg hcoeff hUopen hUconn hUsep hU0 hA
  obtain ⟨dB, hdB_eq⟩ :=
    aRootCount_eventually_const q hmonic hdeg hcoeff hUopen hUconn hUsep hU0 hA.compl
  have hdA : 1 ≤ dA := by
    obtain ⟨y, hy1, hy2⟩ := (hAne.and_eventually hdA_eq).exists; omega
  have hdB : 1 ≤ dB := by
    obtain ⟨y, hy1, hy2⟩ := (hBne.and_eventually hdB_eq).exists; omega
  exact clopen_split_contradiction q hmonic hdeg hcoeff hq0 hsep hε hbdd hirr hUopen hU0 hA hdA hdB
    hdA_eq hdB_eq
