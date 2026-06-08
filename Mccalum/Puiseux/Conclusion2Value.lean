import Mccalum.Puiseux.OrderInvariance

/-!
# Conclusion 2, codim-1 — the order VALUE at the graph section

This file instantiates the capstone `order_eval_eq_min` (Lemma 4.2.8, the value
`order ℂ h = min(m, m₁)`) to the data of the axiom `zariski_order_invariant_in_graph`.

The graph section point is `((y,0), ψ y)` with `ψ` the (locally analytic) single root section from
Conclusion 1. We center the root to `0` by the shifted family `qc y := (q y).comp (X + C (ψ̂ y))`
(`ψ̂` a globally continuous extension of `ψ`, radial-clamped), whose parametrization is `phc := φ − ψ`
(roots shift uniformly). This file builds the coefficient-of-translation machinery needed for the
family hypotheses of `order_eval_eq_min`.
-/

noncomputable section

open Polynomial Filter Metric Set
open scoped Topology

namespace Puiseux

/-- **Coefficient of a translated polynomial** `f.comp (X + C a)` as an explicit finite sum, with a
uniform index range `range (N+1)` valid whenever `f.natDegree < N + 1`. Via `taylor_coeff` and
`hasseDeriv_coeff`. -/
lemma coeff_comp_X_add_C_eq_sum (f : ℂ[X]) (a : ℂ) (k N : ℕ) (hN : f.natDegree < N + 1) :
    (f.comp (X + C a)).coeff k
      = ∑ i ∈ Finset.range (N + 1), ((i + k).choose k : ℂ) * f.coeff (i + k) * a ^ i := by
  rw [← taylor_apply, taylor_coeff,
    eval_eq_sum_range' (n := N + 1)
      (lt_of_le_of_lt (le_trans (natDegree_hasseDeriv_le f k) (Nat.sub_le _ _)) hN)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hasseDeriv_coeff]

variable {n : ℕ}

/-- **Global continuity of the translated family's coefficients.** If `q`'s coefficients are
continuous and the shift `ψ` is continuous, then each coefficient of `qc y = (q y).comp (X + C (ψ y))`
is continuous. -/
lemma continuous_coeff_comp_X_add_C {q : (Fin (n + 1) → ℂ) → ℂ[X]} {m : ℕ}
    (hdeg : ∀ y, (q y).natDegree ≤ m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {ψ : (Fin (n + 1) → ℂ) → ℂ} (hψ : Continuous ψ) (k : ℕ) :
    Continuous (fun y => ((q y).comp (X + C (ψ y))).coeff k) := by
  have heq : (fun y => ((q y).comp (X + C (ψ y))).coeff k)
      = fun y => ∑ i ∈ Finset.range (m + 1),
          ((i + k).choose k : ℂ) * (q y).coeff (i + k) * (ψ y) ^ i :=
    funext fun y => coeff_comp_X_add_C_eq_sum (q y) (ψ y) k m (Nat.lt_succ_of_le (hdeg y))
  rw [heq]
  exact continuous_finset_sum _
    (fun i _ => (continuous_const.mul (hcoeff (i + k))).mul (hψ.pow i))

/-- **Local analyticity of the translated family's coefficients.** At a base point `x` where `q`'s
coefficients and the shift `ψ` are analytic, each coefficient of `qc` is analytic. -/
lemma analyticAt_coeff_comp_X_add_C {q : (Fin (n + 1) → ℂ) → ℂ[X]} {m : ℕ}
    {x : Fin (n + 1) → ℂ} (hdeg : ∀ y, (q y).natDegree ≤ m)
    (hana : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) x)
    {ψ : (Fin (n + 1) → ℂ) → ℂ} (hψ : AnalyticAt ℂ ψ x) (k : ℕ) :
    AnalyticAt ℂ (fun y => ((q y).comp (X + C (ψ y))).coeff k) x := by
  have heq : (fun y => ((q y).comp (X + C (ψ y))).coeff k)
      = fun y => ∑ i ∈ Finset.range (m + 1),
          ((i + k).choose k : ℂ) * (q y).coeff (i + k) * (ψ y) ^ i :=
    funext fun y => coeff_comp_X_add_C_eq_sum (q y) (ψ y) k m (Nat.lt_succ_of_le (hdeg y))
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun i _ => (analyticAt_const.mul (hana (i + k))).mul (hψ.pow i))

/-- **Separability is preserved by the translation** `p ↦ p.comp (X + C a)`. The shear `X ↦ X + a` is
a ring automorphism, so it carries a Bézout identity `u·p + v·p' = 1` to one for `p.comp (X + C a)`
(using `derivative (p.comp (X + C a)) = p'.comp (X + C a)`). Transfers the separability hypotheses of
`order_eval_eq_min` to the centered family `qc`. -/
lemma separable_comp_X_add_C {p : ℂ[X]} (a : ℂ) (hp : p.Separable) :
    (p.comp (X + C a)).Separable := by
  rw [separable_def'] at hp ⊢
  obtain ⟨u, v, huv⟩ := hp
  refine ⟨u.comp (X + C a), v.comp (X + C a), ?_⟩
  have hder : derivative (p.comp (X + C a)) = (derivative p).comp (X + C a) := by
    rw [derivative_comp]; simp
  rw [hder]
  have hcong := congrArg (fun w : ℂ[X] => w.comp (X + C a)) huv
  simpa [add_comp, mul_comp, one_comp] using hcong

/-- **A monic polynomial over `ℂ` with a unique root is a power.** If `p` is monic of degree `m` and
its only root is `α`, then `p = (X − C α)ᵐ`. (`ℂ` splits `p`, so `p = ∏ (X − rootᵢ)` with all roots
`= α`.) This converts Conclusion 1's single-root section into the `hcentral` hypothesis. -/
lemma monic_eq_pow_of_unique_root {p : ℂ[X]} {m : ℕ} {α : ℂ}
    (hmonic : p.Monic) (hdeg : p.natDegree = m)
    (hroot : ∀ β : ℂ, p.IsRoot β ↔ β = α) :
    p = (X - C α) ^ m := by
  have hsplit : p.Splits := by
    simpa using IsAlgClosed.splits_codomain (f := RingHom.id ℂ) p
  have hcard : p.roots.card = m := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, hdeg]
  have hrepl : p.roots = Multiset.replicate m α := by
    rw [Multiset.eq_replicate]
    exact ⟨hcard, fun b hb => (hroot b).mp (Polynomial.mem_roots'.mp hb).2⟩
  calc p = (p.roots.map fun a => X - C a).prod :=
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hcard, hdeg])).symm
    _ = ((Multiset.replicate m α).map fun a => X - C a).prod := by rw [hrepl]
    _ = (Multiset.replicate m (X - C α)).prod := by rw [Multiset.map_replicate]
    _ = (X - C α) ^ m := Multiset.prod_replicate m (X - C α)

section RadialClamp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Radial retraction** onto the closed ball `B̄(0,r)`: continuous everywhere, the identity on
`B(0,r)`, with image in `B̄(0,r)`. Used to globalize the locally-analytic section `ψ` to a globally
continuous `ρ = ψ ∘ radialClamp` (needed for the global-continuity hypothesis of `order_eval_value`). -/
noncomputable def radialClamp (r : ℝ) (y : E) : E := (min r ‖y‖ / ‖y‖) • y

lemma radialClamp_eq_self {r : ℝ} {y : E} (h : ‖y‖ ≤ r) : radialClamp r y = y := by
  rw [radialClamp, min_eq_right h]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [div_self (norm_ne_zero_iff.mpr hy), one_smul]

lemma norm_radialClamp_le {r : ℝ} (hr : 0 ≤ r) (y : E) : ‖radialClamp r y‖ ≤ ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [radialClamp]
  · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [radialClamp, norm_smul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_min hr hyn.le), abs_of_pos hyn,
      div_mul_cancel₀ _ hyn.ne']
    exact min_le_right _ _

lemma norm_radialClamp_le_radius {r : ℝ} (hr : 0 ≤ r) (y : E) : ‖radialClamp r y‖ ≤ r := by
  rcases eq_or_ne y 0 with rfl | hy
  · simpa [radialClamp] using hr
  · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [radialClamp, norm_smul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_min hr hyn.le), abs_of_pos hyn, div_mul_cancel₀ _ hyn.ne']
    exact min_le_left _ _

lemma continuous_radialClamp {r : ℝ} (hr : 0 ≤ r) : Continuous (radialClamp r : E → E) := by
  have hcont0 : ContinuousAt (radialClamp r : E → E) 0 := by
    have hlim : Filter.Tendsto (radialClamp r : E → E) (𝓝 0) (𝓝 0) := by
      refine (tendsto_zero_iff_norm_tendsto_zero).mpr ?_
      refine squeeze_zero (fun y => norm_nonneg _) (fun y => norm_radialClamp_le hr y) ?_
      simpa using (continuous_norm.tendsto (0 : E))
    have h0 : radialClamp r (0 : E) = 0 := by simp [radialClamp]
    rw [ContinuousAt, h0]; exact hlim
  have hcontne : ∀ y : E, y ≠ 0 → ContinuousAt (radialClamp r : E → E) y := by
    intro y hy
    have hyn : Continuous (fun z : E => ‖z‖) := continuous_norm
    refine ContinuousAt.smul ?_ continuousAt_id
    exact ((continuousAt_const.min hyn.continuousAt).div hyn.continuousAt
      (norm_ne_zero_iff.mpr hy))
  refine continuous_iff_continuousAt.mpr (fun y => ?_)
  rcases eq_or_ne y 0 with rfl | hy
  · exact hcont0
  · exact hcontne y hy

end RadialClamp

/-- **Analyticity of the constant coefficient of a translated family along a curve.** If `w ↦ (q (γ w)).coeff i`
is analytic at `0` for every `i`, then so is `w ↦ ((q (γ w)).comp (X + C a)).coeff 0` (a finite
`a`-weighted sum of those coefficients). Used for the `hLHSan0`/`hg0` inputs of `order_eval_eq_min`. -/
lemma analyticAt_coeff0_comp_along {q : (Fin (n + 1) → ℂ) → ℂ[X]} {m : ℕ}
    (hdeg : ∀ y, (q y).natDegree ≤ m) {γ : ℂ → Fin (n + 1) → ℂ} (a : ℂ)
    (hγ : ∀ i, AnalyticAt ℂ (fun w => (q (γ w)).coeff i) 0) :
    AnalyticAt ℂ (fun w => ((q (γ w)).comp (X + C a)).coeff 0) 0 := by
  have heq : (fun w => ((q (γ w)).comp (X + C a)).coeff 0)
      = fun w => ∑ i ∈ Finset.range (m + 1),
          ((i + 0).choose 0 : ℂ) * (q (γ w)).coeff (i + 0) * a ^ i :=
    funext fun w => coeff_comp_X_add_C_eq_sum (q (γ w)) a 0 m (Nat.lt_succ_of_le (hdeg (γ w)))
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun i _ => (analyticAt_const.mul (hγ (i + 0))).mul analyticAt_const)

/-- **The centered branch has finite order** (`hFfin` for `order_eval_value`). If the branch
`φ(z',·)` were constant (`= α` near `0`), every branch difference `φ(z',ζⁱ·) − φ(z',ζʲ·)` would vanish
identically, contradicting `branchDiff_order_ne_top` (which holds by separability / finite disc). Needs
`m ≥ 2` (so distinct indices `i ≠ j` exist). -/
lemma branch_centered_order_ne_top {m : ℕ} (hm2 : 2 ≤ m) {q : (Fin (n + 1) → ℂ) → ℂ[X]}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} (hz' : ‖z'‖ < δz)
    (hsep_punc : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z')).Separable)
    {F : ℂ → ℂ} (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w)) (α : ℂ) :
    analyticOrderAt (fun w => F w - α) 0 ≠ ⊤ := by
  intro htop
  have hm0 : 0 < m := by omega
  have hζne : ζ ≠ 0 := hζ.ne_zero (by omega)
  -- `F = α` near `0`, hence `φ(z',·) = α` on the punctured neighbourhood
  have hFαeq : (fun w => F w - α) =ᶠ[𝓝 (0 : ℂ)] 0 := analyticOrderAt_eq_top.mp htop
  have hFα : F =ᶠ[𝓝 (0 : ℂ)] fun _ => α := by
    filter_upwards [hFαeq] with w hw; exact sub_eq_zero.mp hw
  have hφα : (fun w => φ (z', w)) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => α := by
    filter_upwards [hFeq.symm, hFα.filter_mono nhdsWithin_le_nhds] with w h1 h2
    exact h1.trans h2
  -- scaling `u ↦ ζᵏ u` preserves the punctured neighbourhood, so each branch is `= α` there
  have hscale : ∀ k : ℕ, (fun u => φ (z', ζ ^ k * u)) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => α := by
    intro k
    have htend : Filter.Tendsto (fun u : ℂ => ζ ^ k * u) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Filter.Tendsto (fun u : ℂ => ζ ^ k * u) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mul_ne_zero (pow_ne_zero k hζne) (by simpa using hu)
    filter_upwards [htend.eventually hφα] with u hu; exact hu
  -- the `(0,1)` branch difference vanishes on a full neighbourhood of `0`
  set g : ℂ → ℂ := fun u => φ (z', ζ ^ (0 : ℕ) * u) - φ (z', ζ ^ (1 : ℕ) * u) with hg
  have hgpunc : g =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hscale 0, hscale 1] with u h0 h1
    show φ (z', ζ ^ (0 : ℕ) * u) - φ (z', ζ ^ (1 : ℕ) * u) = 0
    rw [h0, h1, sub_self]
  have hgnhds : g =ᶠ[𝓝 (0 : ℂ)] 0 := by
    rw [← nhdsNE_sup_pure (0 : ℂ)]
    refine Filter.eventually_sup.mpr ⟨hgpunc, ?_⟩
    simp [Filter.eventually_pure, hg]
  -- contradiction with `branchDiff_order_ne_top` for indices `0 ≠ 1` in `Fin m`
  have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hne := branchDiff_order_ne_top hm0 hmonic hdeg hiff hζ hz' hsep_punc hij
  exact hne (analyticOrderAt_eq_top.mpr hgnhds)

/-- **Lemma 4.2.8, the order value at a general graph point.** For a Weierstrass family `q` with
Puiseux parametrization `φ`, whose section root near `z'` is `ρ z` (so `q(cons 0 z) = (X − C(ρ z))ᵐ`,
Conclusion 1), the multivariate order of `h(y,x) = (q y).eval x` at the graph point `(cons 0 z', ρ z')`
is `min(m, m₁)`, where `m₁ = ord` of the *centered* branch `φ(z',·) − ρ z'`.

The proof centers the root to `0` via `order_eval_translate_local` (shear by `ρ ∘ tail`), recognizing
the shifted evaluation as the translated family `qc y = (q y).comp (X + C (ρ (tail y)))`, then applies
the centered capstone `order_eval_eq_min` to `qc` with parametrization `phc = φ − ρ`. -/
theorem order_eval_value {m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → ℂ[X]}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} (hz' : ‖z'‖ < δz)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F 0) (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    {ρ : (Fin n → ℂ) → ℂ} (hρ_cont : Continuous ρ)
    (hρ_ana : ∀ z, ‖z‖ < δz → AnalyticAt ℂ ρ z)
    (hcentral : ∀ᶠ z in 𝓝 z', q (Fin.cons 0 z) = (X - C (ρ z)) ^ m)
    (hFfin : analyticOrderAt (fun w => F w - ρ z') 0 ≠ ⊤)
    (hsep_dir : ∀ v : Fin (n + 1) → ℂ, v 0 ≠ 0 →
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable)
    (hsep_u : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z')).Separable) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', ρ z')
      = min (m : ℕ∞) (analyticOrderAt (fun w => F w - ρ z') 0) := by
  classical
  -- the shear `ψfun y = ρ (tail y)` and the centered family `qc`
  set ψfun : (Fin (n + 1) → ℂ) → ℂ := fun y => ρ (Fin.tail y) with hψfun
  set qc : (Fin (n + 1) → ℂ) → ℂ[X] := fun y => (q y).comp (X + C (ψfun y)) with hqc
  have hψtail : ∀ y : Fin n → ℂ, Fin.tail (Fin.cons (0 : ℂ) y : Fin (n + 1) → ℂ) = y := by
    intro y; simp only [Fin.tail_cons]
  have hψcons0z' : ψfun (Fin.cons 0 z') = ρ z' := by simp only [hψfun, hψtail]
  -- `ψfun` analytic at `cons 0 z'`
  have hψ_an : AnalyticAt ℂ ψfun (Fin.cons 0 z') := by
    have htail_an : AnalyticAt ℂ (fun y : Fin (n + 1) → ℂ => Fin.tail y) (Fin.cons 0 z') :=
      (ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj i.succ) :
        (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt _
    exact (hρ_ana z' hz').comp_of_eq htail_an (hψtail z')
  -- eval-function analytic at the graph point
  have hf_an : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', ρ z') := by
    rw [show (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
        = fun yx => ∑ k ∈ Finset.range (m + 1), (q yx.1).coeff k * yx.2 ^ k from by
      funext yx; exact Polynomial.eval_eq_sum_range' (by rw [hdeg]; omega) yx.2]
    exact Finset.analyticAt_fun_sum _ (fun k _ =>
      (AnalyticAt.comp (g := fun y => (q y).coeff k)
        (f := fun yx : (Fin (n + 1) → ℂ) × ℂ => yx.1) (hana_pt k) analyticAt_fst).mul
        (analyticAt_snd.pow k))
  -- Step 1+2: translate the root to `0`; the shifted eval is `qc`.
  have hstep := order_eval_translate_local (q := q) (z' := z') (ψfun := ψfun) hψ_an
    (by rw [hψcons0z']; exact hf_an)
  rw [hψcons0z'] at hstep
  have hfun : (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval (yx.2 + ψfun yx.1))
      = fun yx => (qc yx.1).eval yx.2 := by
    funext yx; rw [hqc]; simp [Polynomial.eval_comp]
  rw [hfun] at hstep
  rw [hstep]
  -- the centered branch `phc = φ − ρ`
  set phc : (Fin n → ℂ) × ℂ → ℂ := fun zu => φ zu - ρ zu.1 with hphc
  -- `ψfun (cons a z) = ρ z` for any head `a`
  have hψc : ∀ (a : ℂ) (z : Fin n → ℂ), ψfun (Fin.cons a z) = ρ z := fun a z => by
    simp only [hψfun, Fin.tail_cons]
  -- `ψfun` is globally continuous
  have hψfun_cont : Continuous ψfun := by
    rw [hψfun]; exact hρ_cont.comp (continuous_pi (fun i => continuous_apply i.succ))
  -- family hypotheses for `qc`
  have hmonic' : ∀ y, (qc y).Monic := fun y => (hmonic y).comp_X_add_C _
  have hdeg' : ∀ y, (qc y).natDegree = m := fun y => by
    simp only [hqc]; rw [natDegree_comp, natDegree_X_add_C, mul_one, hdeg]
  have hcoeff' : ∀ i, Continuous (fun y => (qc y).coeff i) := fun i =>
    continuous_coeff_comp_X_add_C (fun y => (hdeg y).le) hcoeff hψfun_cont i
  -- parametrization hypotheses for `phc`
  have hroot' : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (qc (Fin.cons (u ^ m) z)).eval (phc (z, u)) = 0 := by
    intro z u hz hu hc'
    rw [hqc]
    simp only [Polynomial.eval_comp, eval_add, eval_X, eval_C]
    rw [show phc (z, u) + ψfun (Fin.cons (u ^ m) z) = φ (z, u) from by
      rw [hψc, hphc]; ring]
    exact hroot z u hz hu hc'
  have han' : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ phc (z, u) := by
    intro z u hz hu hc'
    rw [hphc]
    exact (han z u hz hu hc').sub (AnalyticAt.comp (g := ρ)
      (f := fun zu : (Fin n → ℂ) × ℂ => zu.1) (hρ_ana z hz) analyticAt_fst)
  have hiff' : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((qc (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ phc (z, u') = t) := by
    intro z u t hz hu hc'
    rw [hqc]
    simp only [Polynomial.eval_comp, eval_add, eval_X, eval_C]
    rw [hψc, hiff z u (t + ρ z) hz hu hc']
    refine exists_congr (fun u' => and_congr_right (fun _ => ?_))
    rw [hphc]
    exact sub_eq_iff_eq_add.symm
  -- the centered branch order and its slice
  have hFan' : AnalyticAt ℂ (fun w => F w - ρ z') 0 := hFan.sub analyticAt_const
  have hFeq' : (fun w => F w - ρ z') =ᶠ[𝓝[≠] (0 : ℂ)] fun w => phc (z', w) := by
    filter_upwards [hFeq] with w hw
    rw [hphc]; show F w - ρ z' = φ (z', w) - ρ z'; rw [hw]
  have hcentral' : ∀ᶠ z in 𝓝 z', qc (Fin.cons 0 z) = X ^ m := by
    filter_upwards [hcentral] with z hz
    rw [hqc]
    show (q (Fin.cons 0 z)).comp (X + C (ψfun (Fin.cons 0 z))) = X ^ m
    rw [hz, hψc, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have hana_pt' : ∀ i, AnalyticAt ℂ (fun y => (qc y).coeff i) (Fin.cons 0 z') := fun i =>
    analyticAt_coeff_comp_X_add_C (fun y => (hdeg y).le) hana_pt hψ_an i
  have hsep_dir' : ∀ v : Fin (n + 1) → ℂ, v 0 ≠ 0 →
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (qc (Fin.cons 0 z' + s ^ m • v)).Separable := by
    intro v hv0
    filter_upwards [hsep_dir v hv0] with s hs
    rw [hqc]; exact separable_comp_X_add_C _ hs
  have hsep_u' : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (qc (Fin.cons (u ^ m) z')).Separable := by
    filter_upwards [hsep_u] with u hu
    rw [hqc]; exact separable_comp_X_add_C _ hu
  -- curve analyticity for the `coeff 0` slices
  have hcons_pow_ana : AnalyticAt ℂ (fun u : ℂ => (Fin.cons (u ^ m) z' : Fin (n + 1) → ℂ)) 0 := by
    rw [show (fun u : ℂ => (Fin.cons (u ^ m) z' : Fin (n + 1) → ℂ))
        = fun u => Fin.cons 0 z' + (u ^ m) • (Pi.single 0 1 : Fin (n + 1) → ℂ) from by
      funext u j; refine Fin.cases ?_ (fun i => ?_) j <;>
        simp [Fin.cons_zero, Fin.cons_succ, Pi.single]]
    exact analyticAt_const.add ((analyticAt_id.pow m).smul analyticAt_const)
  have hcons_id_ana : AnalyticAt ℂ (fun w : ℂ => (Fin.cons w z' : Fin (n + 1) → ℂ)) 0 := by
    rw [show (fun w : ℂ => (Fin.cons w z' : Fin (n + 1) → ℂ))
        = fun w => Fin.cons 0 z' + w • (Pi.single 0 1 : Fin (n + 1) → ℂ) from by
      funext w j; refine Fin.cases ?_ (fun i => ?_) j <;>
        simp [Fin.cons_zero, Fin.cons_succ, Pi.single]]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hLHSan0' : AnalyticAt ℂ (fun u => (qc (Fin.cons (u ^ m) z')).coeff 0) 0 := by
    have hγ : ∀ i, AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z')).coeff i) 0 := fun i =>
      AnalyticAt.comp_of_eq (hana_pt i) hcons_pow_ana (by rw [zero_pow hm.ne'])
    rw [show (fun u => (qc (Fin.cons (u ^ m) z')).coeff 0)
        = fun u => ((q (Fin.cons (u ^ m) z')).comp (X + C (ρ z'))).coeff 0 from by
      funext u; simp only [hqc, hψc]]
    exact analyticAt_coeff0_comp_along (fun y => (hdeg y).le) (ρ z') hγ
  have hg0' : AnalyticAt ℂ (fun w => (qc (Fin.cons w z')).coeff 0) 0 := by
    have hγ : ∀ i, AnalyticAt ℂ (fun w => (q (Fin.cons w z')).coeff i) 0 := fun i =>
      AnalyticAt.comp_of_eq (hana_pt i) hcons_id_ana rfl
    rw [show (fun w => (qc (Fin.cons w z')).coeff 0)
        = fun w => ((q (Fin.cons w z')).comp (X + C (ρ z'))).coeff 0 from by
      funext w; simp only [hqc, hψc]]
    exact analyticAt_coeff0_comp_along (fun y => (hdeg y).le) (ρ z') hγ
  exact order_eval_eq_min hm hmonic' hdeg' hcoeff' hroot' han' hiff' hζ hz'
    hFan' hFeq' hFfin hcentral' hana_pt' hsep_dir' hLHSan0' hsep_u' hg0'

end Puiseux
