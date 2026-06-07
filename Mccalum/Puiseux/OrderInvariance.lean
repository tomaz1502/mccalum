import Mccalum.Puiseux.ParametrizationFamily
import Mccalum.Generalized.RootBound
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Order-invariance via continuity of Cauchy coefficients (route 3)

The codim-1 order-invariance (Zariski 4.1.1, conclusion 2 / Lemmas 4.2.7–4.2.8) is proved here
**analytically**, using the existing Newton–Puiseux parametrization `φ(z,u)` (`exists_param_family`)
together with **continuity** (not analyticity) of the Cauchy-integral coefficients of the analytic
branches. This sidesteps both the formal-Puiseux machinery and the several-variable
analyticity (Hartogs) gap: every place that needs regularity in the section variable `z` needs only
*continuity*, which follows from `continuous_parametric_intervalIntegral_of_continuous'`.

This file starts with the linchpin: a Cauchy-type coefficient `z ↦ ∮_{|u|=ρ} F(z,u)·uᵏ du` is
continuous in `z` whenever `F` is jointly continuous.
-/

noncomputable section

open Filter Topology Complex MeasureTheory intervalIntegral
open scoped Real

namespace Puiseux

/-- **Linchpin (continuity of a parametrized circle integral).** If `F` is jointly continuous, then
the Cauchy-type coefficient `z ↦ ∮_{|u|=ρ} F z u · uᵏ du` (over a fixed circle of radius `ρ > 0`) is
continuous in the parameter `z`. The integrand is jointly continuous (the contour avoids `0`, so the
integer power `uᵏ` is continuous), so `continuous_parametric_intervalIntegral_of_continuous'` applies. -/
theorem continuous_circleIntegral_param {W : Type*} [TopologicalSpace W]
    {F : W → ℂ → ℂ} (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ {u : ℂ | u ≠ 0}))
    {ρ : ℝ} (hρ : 0 < ρ) (k : ℤ) :
    Continuous (fun z => ∮ u in C(0, ρ), F z u * u ^ k) := by
  have hcm : Continuous fun p : W × ℝ => circleMap 0 ρ p.2 :=
    (continuous_circleMap 0 ρ).comp continuous_snd
  have hne : ∀ p : W × ℝ, circleMap 0 ρ p.2 ≠ 0 := fun p => circleMap_ne_center hρ.ne'
  have hF' : Continuous fun p : W × ℝ => F p.1 (circleMap 0 ρ p.2) :=
    hF.comp_continuous (continuous_fst.prodMk hcm)
      (fun p => Set.mk_mem_prod (Set.mem_univ _) (hne p))
  have hint : Continuous (Function.uncurry fun (z : W) (θ : ℝ) =>
      deriv (circleMap 0 ρ) θ • (F z (circleMap 0 ρ θ) * circleMap 0 ρ θ ^ k)) := by
    simp only [Function.uncurry_def, deriv_circleMap, smul_eq_mul]
    exact ((hcm.mul continuous_const).mul
      (hF'.mul (hcm.zpow₀ k (fun p => Or.inl (hne p)))))
  exact continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * π)

/-- **Order bound from a nonzero Cauchy coefficient.** If `g` is analytic on `ball 0 R`, `ρ ∈ (0,R)`,
and the `K`-th Cauchy coefficient `∮_{|u|=ρ} g(u)·u^(-K-1) du ≠ 0`, then `g` vanishes to order `≤ K`
at `0`. (Contrapositive: if `g` vanishes to order `> K`, then `g(u)·u^(-K-1)` extends analytically
across `0`, so its circle integral is `0` by Cauchy–Goursat.) This is the engine of the
upper-semicontinuity step in Lemma 4.2.7. -/
theorem analyticOrderAt_le_of_circleIntegral_ne {g : ℂ → ℂ} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R)) (K : ℕ)
    (hne : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) ≠ 0) :
    analyticOrderAt g 0 ≤ (K : ℕ∞) := by
  by_contra h
  rw [not_le] at h
  have hK1 : ((K + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 := by
    rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt h
  have hg0 : AnalyticAt ℂ g 0 := hg 0 (Metric.mem_ball_self (lt_trans hρ hρR))
  obtain ⟨g₁, hg₁an, hfac⟩ := (natCast_le_analyticOrderAt hg0).mp hK1
  set G : ℂ → ℂ := Function.update (fun u => g u * u ^ (-(K : ℤ) - 1)) 0 (g₁ 0) with hG
  -- `G` agrees with `g₁` near `0`
  have hGg₁ : G =ᶠ[𝓝 0] g₁ := by
    filter_upwards [hfac] with u hu
    rcases eq_or_ne u 0 with rfl | hune
    · rw [hG, Function.update_self]
    · rw [hG, Function.update_of_ne hune, hu, sub_zero, smul_eq_mul, ← zpow_natCast u (K + 1)]
      have hexp : ((K + 1 : ℕ) : ℤ) + (-(K : ℤ) - 1) = 0 := by push_cast; ring
      have hpow : (u : ℂ) ^ ((K + 1 : ℕ) : ℤ) * u ^ (-(K : ℤ) - 1) = 1 := by
        rw [← zpow_add₀ hune, hexp, zpow_zero]
      linear_combination g₁ u * hpow
  -- `G` is analytic on `ball 0 R`
  have hGan : AnalyticOnNhd ℂ G (Metric.ball 0 R) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hune
    · exact (hg₁an.congr hGg₁.symm)
    · have : G =ᶠ[𝓝 u] fun v => g v * v ^ (-(K : ℤ) - 1) := by
        filter_upwards [eventually_nhds_iff.mpr ⟨{0}ᶜ, fun _ h => h, isOpen_compl_singleton,
          Set.mem_compl_singleton_iff.mpr hune⟩] with v hv
        have hv' : v ≠ 0 := hv
        rw [hG, Function.update_of_ne hv']
      refine AnalyticAt.congr ?_ this.symm
      exact (hg u hu).mul (analyticAt_id.zpow hune)
  -- the circle integral of `g·u^(-K-1)` equals that of the analytic `G`, which is `0`
  have hcong : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) = ∮ u in C(0, ρ), G u := by
    refine circleIntegral.integral_congr hρ.le (fun u hu => ?_)
    have hune : u ≠ 0 := by
      rw [Metric.mem_sphere, dist_zero_right] at hu; rw [← norm_pos_iff, hu]; exact hρ
    rw [hG, Function.update_of_ne hune]
  have hzero : (∮ u in C(0, ρ), G u) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hρ.le ?_
    refine DiffContOnCl.mk ?_ ?_
    · intro u hu
      exact ((hGan u (Metric.ball_subset_ball hρR.le hu)).differentiableAt).differentiableWithinAt
    · refine (hGan.continuousOn).mono ?_
      rw [closure_ball 0 hρ.ne']
      exact Metric.closedBall_subset_ball hρR
  rw [hcong, hzero] at hne
  exact hne rfl

/-- **Nonzero Cauchy coefficient at the exact order.** If `g` is analytic on `ball 0 R`, `ρ ∈ (0,R)`,
and `g` vanishes to order *exactly* `K` at `0`, then the `K`-th Cauchy coefficient
`∮_{|u|=ρ} g(u)·u^(-K-1) du = 2πi·g₁(0) ≠ 0` (where `g = uᴷ·g₁`, `g₁(0) ≠ 0`). Dual to
`analyticOrderAt_le_of_circleIntegral_ne`; together they give upper-semicontinuity of the order. -/
theorem circleIntegral_ne_of_analyticOrderAt_eq {g : ℂ → ℂ} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R)) (K : ℕ)
    (hord : analyticOrderAt g 0 = (K : ℕ∞)) :
    (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) ≠ 0 := by
  have hg0 : AnalyticAt ℂ g 0 := hg 0 (Metric.mem_ball_self (lt_trans hρ hρR))
  obtain ⟨g₁, hg₁an, hg₁0, hfac⟩ := hg0.analyticOrderAt_eq_natCast.mp hord
  set G : ℂ → ℂ := Function.update (fun u => g u * u ^ (-(K : ℤ))) 0 (g₁ 0) with hG
  have hG0 : G 0 = g₁ 0 := Function.update_self _ _ _
  have hGg₁ : G =ᶠ[𝓝 0] g₁ := by
    filter_upwards [hfac] with u hu
    rcases eq_or_ne u 0 with rfl | hune
    · rw [hG, Function.update_self]
    · rw [hG, Function.update_of_ne hune, hu, sub_zero, smul_eq_mul, ← zpow_natCast u K]
      have hexp : ((K : ℕ) : ℤ) + (-(K : ℤ)) = 0 := by ring
      have hpow : (u : ℂ) ^ ((K : ℕ) : ℤ) * u ^ (-(K : ℤ)) = 1 := by
        rw [← zpow_add₀ hune, hexp, zpow_zero]
      linear_combination g₁ u * hpow
  have hGan : AnalyticOnNhd ℂ G (Metric.ball 0 R) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hune
    · exact hg₁an.congr hGg₁.symm
    · have : G =ᶠ[𝓝 u] fun v => g v * v ^ (-(K : ℤ)) := by
        filter_upwards [eventually_nhds_iff.mpr ⟨{0}ᶜ, fun _ h => h, isOpen_compl_singleton,
          Set.mem_compl_singleton_iff.mpr hune⟩] with v hv
        have hv' : v ≠ 0 := hv
        rw [hG, Function.update_of_ne hv']
      exact AnalyticAt.congr ((hg u hu).mul (analyticAt_id.zpow hune)) this.symm
  -- rewrite the `K`-th coefficient integral as a value integral for `G`
  have hval : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) = ∮ u in C(0, ρ), (u - 0)⁻¹ • G u := by
    refine circleIntegral.integral_congr hρ.le (fun u hu => ?_)
    have hune : u ≠ 0 := by
      rw [Metric.mem_sphere, dist_zero_right] at hu; rw [← norm_pos_iff, hu]; exact hρ
    have hpow2 : (u : ℂ) ^ (-(K : ℤ) - 1) = u⁻¹ * u ^ (-(K : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add₀ hune]; congr 1; ring
    rw [hG, Function.update_of_ne hune, sub_zero, smul_eq_mul, hpow2]; ring
  -- Cauchy integral formula for the value
  have hformula : ((2 * π * I : ℂ)⁻¹ • ∮ u in C(0, ρ), (u - 0)⁻¹ • G u) = G 0 :=
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty (Metric.mem_ball_self hρ)
      ((hGan.continuousOn).mono (Metric.closedBall_subset_ball hρR))
      (fun u hu => (hGan u (Metric.ball_subset_ball hρR.le hu.1)).differentiableAt)
  intro hcontra
  rw [hval] at hcontra
  rw [hcontra, smul_zero, hG0] at hformula
  exact hg₁0 hformula.symm

/-- **Upper-semicontinuity of the vanishing order in a continuous family.** If `g : W → ℂ → ℂ` is
jointly continuous, each slice `g z` is analytic on a common disc `ball 0 R`, and the slice at `z₀`
vanishes to order exactly `K`, then nearby slices vanish to order `≤ K`. (The `K`-th Cauchy
coefficient is `≠ 0` at `z₀` and continuous, hence `≠ 0` nearby, forcing order `≤ K`.) This is the
engine of the constancy step in Lemma 4.2.7. -/
theorem analyticOrderAt_le_eventually {W : Type*} [TopologicalSpace W] {g : W → ℂ → ℂ}
    (hg : ContinuousOn (Function.uncurry g) (Set.univ ×ˢ {u : ℂ | u ≠ 0}))
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {z₀ : W}
    (hgan : ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ (g z) (Metric.ball 0 R)) {K : ℕ}
    (hord : analyticOrderAt (g z₀) 0 = (K : ℕ∞)) :
    ∀ᶠ z in 𝓝 z₀, analyticOrderAt (g z) 0 ≤ (K : ℕ∞) := by
  have hgz₀ : AnalyticOnNhd ℂ (g z₀) (Metric.ball 0 R) := hgan.self_of_nhds
  have hc0 : (∮ u in C(0, ρ), g z₀ u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    circleIntegral_ne_of_analyticOrderAt_eq hρ hρR hgz₀ K hord
  have hcont : Continuous (fun z => ∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) :=
    continuous_circleIntegral_param hg hρ (-(K : ℤ) - 1)
  have hev : ∀ᶠ z in 𝓝 z₀, (∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    hcont.continuousAt.eventually_ne hc0
  filter_upwards [hev, hgan] with z hz hzan
  exact analyticOrderAt_le_of_circleIntegral_ne hρ hρR hzan K hz

/-- **Local continuity of a parametrized circle integral.** If `F` is jointly continuous on
`S ×ˢ {u ≠ 0}` for some neighbourhood `S` of `z₀`, then the Cauchy-type coefficient
`z ↦ ∮_{|u|=ρ} F z u · uᵏ du` is continuous *at* `z₀`. This is the local form of
`continuous_circleIntegral_param` (which it reuses, restricting to the open subtype `interior S`):
the Puiseux branches are only continuous on a bounded region, so only a *local* hypothesis is
available. -/
theorem continuousAt_circleIntegral_param {W : Type*} [TopologicalSpace W]
    {F : W → ℂ → ℂ} {z₀ : W} {S : Set W} {T : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T) (hS : S ∈ 𝓝 z₀)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ T)) (k : ℤ) :
    ContinuousAt (fun z => ∮ u in C(0, ρ), F z u * u ^ k) z₀ := by
  have hz₀U : z₀ ∈ interior S := mem_interior_iff_mem_nhds.mpr hS
  have hcm : Continuous fun p : ↥(interior S) × ℝ => circleMap 0 ρ p.2 :=
    (continuous_circleMap 0 ρ).comp continuous_snd
  have hne : ∀ p : ↥(interior S) × ℝ, circleMap 0 ρ p.2 ≠ 0 := fun _ => circleMap_ne_center hρ.ne'
  have hmap : ∀ p : ↥(interior S) × ℝ, ((p.1.val, circleMap 0 ρ p.2) : W × ℂ) ∈ S ×ˢ T :=
    fun p => Set.mk_mem_prod (interior_subset p.1.2) (hT p.2)
  have hF' : Continuous fun p : ↥(interior S) × ℝ => F p.1.val (circleMap 0 ρ p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk hcm) hmap
  have hint : Continuous (Function.uncurry fun (z : ↥(interior S)) (θ : ℝ) =>
      deriv (circleMap 0 ρ) θ • (F z.val (circleMap 0 ρ θ) * circleMap 0 ρ θ ^ k)) := by
    simp only [Function.uncurry_def, deriv_circleMap, smul_eq_mul]
    exact ((hcm.mul continuous_const).mul (hF'.mul (hcm.zpow₀ k (fun p => Or.inl (hne p)))))
  have hcont : Continuous (fun z : ↥(interior S) => ∮ u in C(0, ρ), F z.val u * u ^ k) :=
    continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * π)
  have hrestr : ContinuousOn (fun z => ∮ u in C(0, ρ), F z u * u ^ k) (interior S) := by
    rw [continuousOn_iff_continuous_restrict]; exact hcont
  exact hrestr.continuousAt (isOpen_interior.mem_nhds hz₀U)

/-- **Upper-semicontinuity of the vanishing order (local form).** Like
`analyticOrderAt_le_eventually`, but the joint continuity of `g` is only required on
`S ×ˢ {u ≠ 0}` for a neighbourhood `S` of `z₀`. This is the form usable for the Puiseux branches,
which are analytic only on a bounded region. -/
theorem analyticOrderAt_le_eventually_local {W : Type*} [TopologicalSpace W] {g : W → ℂ → ℂ}
    {z₀ : W} {S : Set W} {T : Set ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T) (hS : S ∈ 𝓝 z₀)
    (hg : ContinuousOn (Function.uncurry g) (S ×ˢ T))
    (hgan : ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ (g z) (Metric.ball 0 R)) {K : ℕ}
    (hord : analyticOrderAt (g z₀) 0 = (K : ℕ∞)) :
    ∀ᶠ z in 𝓝 z₀, analyticOrderAt (g z) 0 ≤ (K : ℕ∞) := by
  have hgz₀ : AnalyticOnNhd ℂ (g z₀) (Metric.ball 0 R) := hgan.self_of_nhds
  have hc0 : (∮ u in C(0, ρ), g z₀ u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    circleIntegral_ne_of_analyticOrderAt_eq hρ hρR hgz₀ K hord
  have hcont : ContinuousAt (fun z => ∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) z₀ :=
    continuousAt_circleIntegral_param hρ hT hS hg (-(K : ℤ) - 1)
  have hev : ∀ᶠ z in 𝓝 z₀, (∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    hcont.eventually_ne hc0
  filter_upwards [hev, hgan] with z hz hzan
  exact analyticOrderAt_le_of_circleIntegral_ne hρ hρR hzan K hz

/-! ### Puiseux branches and the discriminant identity (Lemma 4.2.7 setup) -/

/-- **The `m`-th roots of `uᵐ` are exactly the branch points `ζⁱ·u`.** For a primitive `m`-th root of
unity `ζ` and `u ≠ 0`, `u'ᵐ = uᵐ ↔ u' = ζⁱ·u` for some `i ∈ Fin m`. This underlies the indexed Puiseux
branches `θᵢ(z,u) = φ(z, ζⁱu)`. -/
theorem pow_eq_pow_iff_branch {ζ : ℂ} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    {u u' : ℂ} (hu : u ≠ 0) :
    u' ^ m = u ^ m ↔ ∃ i : Fin m, u' = ζ ^ (i : ℕ) * u := by
  haveI : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro h
    have hpow1 : (u' / u) ^ m = 1 := by rw [div_pow, h, div_self (pow_ne_zero m hu)]
    obtain ⟨i, hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hpow1
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [hpow]; field_simp
  · rintro ⟨i, rfl⟩
    rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

open Polynomial in
/-- **Discriminant as a product of root-differences.** For a monic complex polynomial `p` of positive
degree, `discr p = ±∏_{x ∈ roots} ∏_{s ∈ roots.erase x} (x - s)` (the sign is `(-1)^(d(d-1)/2)`).
Derived from `discr = ±resultant(p, p')`, `resultant = ∏ p'(roots)` (monic, splits over `ℂ`), and
`p'(x) = ∏_{s ≠ x}(x - s)` at each root. The order-in-a-parameter of this product is `2·Σ_{i<j}` the
orders of the root-differences — the discriminant–branch relation `r = 2·Σ O(η_{ij})` of Lemma 4.2.7. -/
theorem discr_eq_prod_roots {p : Polynomial ℂ} (hm : p.Monic) (hpos : 0 < p.natDegree) :
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod := by
  classical
  set k := p.natDegree * (p.natDegree - 1) / 2 with hk
  have hsp : p.Splits := IsAlgClosed.splits p
  have hdeg_pos : 0 < p.degree := by
    rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hpos
  have hdeg_der : (derivative p).natDegree = p.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq p hpos)
  have hres_eq : resultant p (derivative p) p.natDegree (derivative p).natDegree
      = (-1) ^ k * p.discr := by
    rw [hdeg_der, resultant_deriv hdeg_pos, hm.leadingCoeff, mul_one]
  have hres_prod : resultant p (derivative p) p.natDegree (derivative p).natDegree
      = (p.roots.map (fun x => (derivative p).eval x)).prod := by
    rw [resultant_eq_prod_eval p (derivative p) (derivative p).natDegree le_rfl hsp,
      hm.leadingCoeff, one_pow, one_mul]
  have heval : (p.roots.map (fun x => (derivative p).eval x)).prod
      = (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod :=
    congrArg Multiset.prod (Multiset.map_congr rfl (fun x hx => hsp.eval_root_derivative hm hx))
  have h1 : (-1 : ℂ) ^ k * p.discr
      = (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod := by
    rw [← hres_eq, hres_prod, heval]
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc p.discr = ((-1 : ℂ) ^ k * (-1) ^ k) * p.discr := by rw [hsq, one_mul]
    _ = (-1) ^ k * ((-1) ^ k * p.discr) := by ring
    _ = _ := by rw [h1]

/-- **Ramification multiplies the order.** For `f` analytic at `0` and `m ≥ 1`, the order of
`u ↦ f(uᵐ)` at `0` is `m` times the order of `f` at `0` (substituting `w = uᵐ` scales the leading
exponent by `m`). Turns `ord_w disc` into `ord_u disc(z, uᵐ)`. -/
theorem analyticOrderAt_comp_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {m : ℕ} (hm : 0 < m) :
    analyticOrderAt (fun u => f (u ^ m)) 0 = m * analyticOrderAt f 0 := by
  have h0m : (0 : ℂ) ^ m = 0 := zero_pow hm.ne'
  have htend : Filter.Tendsto (fun u : ℂ => u ^ m) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun u : ℂ => u ^ m) (𝓝 0) (𝓝 ((0 : ℂ) ^ m)) :=
      (continuous_pow m).tendsto 0
    rwa [h0m] at h
  have hpm : AnalyticAt ℂ (fun u : ℂ => u ^ m) 0 := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow m
  have hfm : AnalyticAt ℂ (fun u => f (u ^ m)) 0 :=
    AnalyticAt.comp (g := f) (f := fun u : ℂ => u ^ m)
      (by show AnalyticAt ℂ f ((0 : ℂ) ^ m); rw [h0m]; exact hf) hpm
  rcases eq_or_ne (analyticOrderAt f 0) ⊤ with htop | hfin
  · rw [htop, ENat.mul_top (by exact_mod_cast hm.ne')]
    rw [analyticOrderAt_eq_top] at htop ⊢
    exact htend.eventually htop
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f 0 = (n : ℕ∞) := ⟨_, (ENat.coe_toNat hfin).symm⟩
    obtain ⟨g, hgan, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hn
    rw [hn, ← Nat.cast_mul]
    refine hfm.analyticOrderAt_eq_natCast.mpr ⟨fun u => g (u ^ m), ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (g := g) (f := fun u : ℂ => u ^ m)
        (by show AnalyticAt ℂ g ((0 : ℂ) ^ m); rw [h0m]; exact hgan) hpm
    · simpa [h0m] using hg0
    · filter_upwards [htend.eventually hfac] with u hu
      simp only [sub_zero] at hu ⊢
      rw [hu, ← pow_mul]

/-- **Reindexing the discriminant product over an injective root family.** If `r : Fin m → ℂ` is
injective, the multiset double-product `∏_{x∈image}∏_{s∈image∖x}(x-s)` from `discr_eq_prod_roots`
equals the indexed double-product `∏ᵢ ∏_{j≠i} (rᵢ - rⱼ)`. -/
theorem prod_roots_erase_eq_prod_fin {m : ℕ} {r : Fin m → ℂ} (hr : Function.Injective r) :
    ((Finset.univ.val.map r).map
        (fun x => (((Finset.univ.val.map r).erase x).map (fun s => x - s)).prod)).prod
      = ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
  classical
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [← Multiset.map_erase r hr, Multiset.map_map, ← Finset.erase_val,
    ← Finset.prod_eq_multiset_prod]
  rfl

/-- If `a k ≤ b k` (finite) for all `k` and `∑ a = ∑ b`, then `a k = b k` for each `k`. The
"sum-constancy forces termwise constancy" step of Lemma 4.2.7. -/
theorem enat_eq_of_le_of_sum_eq {κ : Type*} [Fintype κ] {a b : κ → ℕ∞}
    (hle : ∀ k, a k ≤ b k) (hb : ∀ k, b k ≠ ⊤) (hsum : ∑ k, a k = ∑ k, b k) (k : κ) :
    a k = b k := by
  have ha : ∀ j, a j ≠ ⊤ := fun j => (lt_of_le_of_lt (hle j) (hb j).lt_top).ne
  have hac : ∀ j, ((a j).toNat : ℕ∞) = a j := fun j => ENat.coe_toNat (ha j)
  have hbc : ∀ j, ((b j).toNat : ℕ∞) = b j := fun j => ENat.coe_toNat (hb j)
  have hle' : ∀ j, (a j).toNat ≤ (b j).toNat := fun j => by
    rw [← Nat.cast_le (α := ℕ∞), hac, hbc]; exact hle j
  have hsum' : ∑ j, (a j).toNat = ∑ j, (b j).toNat := by
    have h : (↑(∑ j, (a j).toNat) : ℕ∞) = ↑(∑ j, (b j).toNat) := by
      rw [Nat.cast_sum, Nat.cast_sum]; simp only [hac, hbc]; exact hsum
    exact_mod_cast h
  by_contra hne
  have hlt : (a k).toNat < (b k).toNat :=
    lt_of_le_of_ne (hle' k) (fun h => hne (by rw [← hac, ← hbc, h]))
  exact absurd hsum' (ne_of_lt
    (Finset.sum_lt_sum (fun j _ => hle' j) ⟨k, Finset.mem_univ k, hlt⟩))

/-- **Lemma 4.2.7 core (abstract constancy of branch-difference orders).** Given a finite family of
"branch differences" `η k : (Fin n → ℂ) → ℂ → ℂ`, each jointly continuous off `u = 0` and per-slice
analytic on a common disc, with the **sum** of their orders constant near `z₀` (this is the
discriminant relation `ord disc = Σ O(η_{ij})` together with `hdisc`), and each order finite at `z₀`,
then **each** order is individually constant near `z₀`. Engine `analyticOrderAt_le_eventually` gives
`≤` termwise; the constant sum upgrades `≤` to `=`. -/
theorem branch_order_constant {n : ℕ} {κ : Type*} [Fintype κ]
    {η : κ → (Fin n → ℂ) → ℂ → ℂ} {z₀ : Fin n → ℂ} {S : Set (Fin n → ℂ)} {T : Set ℂ}
    (hS : S ∈ 𝓝 z₀) {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T)
    (hcont : ∀ k, ContinuousOn (Function.uncurry (η k)) (S ×ˢ T))
    (hana : ∀ k, ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ (η k z) (Metric.ball 0 R))
    (hfin : ∀ k, analyticOrderAt (η k z₀) 0 ≠ ⊤)
    (hsumconst : ∀ᶠ z in 𝓝 z₀,
      ∑ k, analyticOrderAt (η k z) 0 = ∑ k, analyticOrderAt (η k z₀) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ k, analyticOrderAt (η k z) 0 = analyticOrderAt (η k z₀) 0 := by
  have hk : ∀ k, ∀ᶠ z in 𝓝 z₀,
      analyticOrderAt (η k z) 0 ≤ analyticOrderAt (η k z₀) 0 := by
    intro k
    have hKeq : analyticOrderAt (η k z₀) 0 = (((analyticOrderAt (η k z₀) 0).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat (hfin k)).symm
    have h := analyticOrderAt_le_eventually_local hρ hρR hT hS (hcont k) (hana k) hKeq
    rwa [← hKeq] at h
  filter_upwards [Filter.eventually_all.mpr hk, hsumconst] with z hzle hzsum
  exact fun k => enat_eq_of_le_of_sum_eq hzle hfin hzsum k

open Polynomial in
/-- **Discriminant of the Weierstrass family as a product of branch-differences.** At a separable
point `u ≠ 0`, the discriminant of `q(cons(uᵐ, z))` equals `±∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` — the
concrete instantiation of `discr_eq_prod_roots` + `prod_roots_erase_eq_prod_fin`, using that the roots
are exactly the (distinct) Puiseux branches `φ(z,ζⁱu)` (parametrization iff + `pow_eq_pow_iff_branch`,
distinctness from separability). -/
theorem weierstrass_disc_eq_prod_branches {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z : Fin n → ℂ} {u : ℂ} (hz : ‖z‖ < δz) (hu : 0 < ‖u‖) (hud : ‖u‖ ^ m < Real.exp c)
    (hsepu : (q (Fin.cons (u ^ m) z)).Separable) :
    (q (Fin.cons (u ^ m) z)).discr
      = (-1) ^ (m * (m - 1) / 2)
        * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) := by
  classical
  set p := q (Fin.cons (u ^ m) z) with hp
  set r : Fin m → ℂ := fun i => φ (z, ζ ^ (i : ℕ) * u) with hr
  have hpne : p ≠ 0 := (hmonic _).ne_zero
  have hpm : p.natDegree = m := hdeg _
  have hpdeg : 0 < p.natDegree := by rw [hpm]; exact hm
  have hmem : ∀ x, x ∈ p.roots ↔ ∃ i : Fin m, r i = x := by
    intro x
    rw [mem_roots hpne, IsRoot.def, hiff z u x hz hu hud]
    constructor
    · rintro ⟨u', hu'm, hu'φ⟩
      obtain ⟨i, hi⟩ := (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mp hu'm
      exact ⟨i, by show φ (z, ζ ^ (i : ℕ) * u) = x; rw [← hi]; exact hu'φ⟩
    · rintro ⟨i, hi⟩
      exact ⟨ζ ^ (i : ℕ) * u, (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mpr ⟨i, rfl⟩, hi⟩
  have hrootcard : p.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepu),
      (splits_iff_card_roots.mp (IsAlgClosed.splits p)), hpm]
  have himg : Finset.image r Finset.univ = p.roots.toFinset := by
    ext x
    rw [Finset.mem_image, Multiset.mem_toFinset, hmem x]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩⟩
  have hrinj : Function.Injective r := by
    rw [← Set.injOn_univ, ← Finset.coe_univ]
    refine Finset.injOn_of_card_image_eq ?_
    rw [himg, hrootcard, Finset.card_univ, Fintype.card_fin]
  have hroots : p.roots = Finset.univ.val.map r := by
    refine (Multiset.Nodup.ext (nodup_roots hsepu) (Finset.univ.nodup.map hrinj)).mpr ?_
    intro x
    rw [hmem x, Multiset.mem_map]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ_val i, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [discr_eq_prod_roots (hmonic _) hpdeg, hroots, prod_roots_erase_eq_prod_fin hrinj, hpm]

/-- **Order of a finite product is the sum of orders** (1-variable analytic functions). -/
theorem analyticOrderAt_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) :
    (∀ i ∈ s, AnalyticAt ℂ (f i) 0) →
      analyticOrderAt (fun u => ∏ i ∈ s, f i u) 0 = ∑ i ∈ s, analyticOrderAt (f i) 0 := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [analyticOrderAt_eq_zero]
  | @insert a s ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, AnalyticAt ℂ (f i) 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprodan : AnalyticAt ℂ (fun u => ∏ i ∈ s, f i u) 0 := Finset.analyticAt_fun_prod s hfs
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [show (fun u => f a u * ∏ i ∈ s, f i u) = (f a) * (fun u => ∏ i ∈ s, f i u) from rfl,
      analyticOrderAt_mul hfa hprodan, ih hfs]

/-! ### Step A — branches: per-slice analytic extension, continuity, and finiteness -/

open Polynomial in
/-- **Per-slice removable singularity.** For a Weierstrass family `q` and its Puiseux
parametrization `φ` (root + slice-analyticity hypotheses), each slice `w ↦ φ(z, w)` (`‖z‖ < δz`)
is bounded near `0` (its values are roots of `q(cons(wᵐ, z))`, bounded by the Cauchy bound) and
analytic on the punctured disc, hence extends to a function `F` analytic *at* `0`. -/
theorem exists_phi_slice_extend {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z : Fin n → ℂ} (hz : ‖z‖ < δz) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F =ᶠ[𝓝[≠] (0 : ℂ)] (fun w => φ (z, w)) := by
  -- the punctured region near `0`
  have hexp : (0 : ℝ) < Real.exp c := Real.exp_pos c
  have hlt : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖w‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun w : ℂ => ‖w‖ ^ m) 0 :=
      (continuous_norm.pow m).continuousAt
    have h0 : (fun w : ℂ => ‖w‖ ^ m) 0 < Real.exp c := by simpa [zero_pow hm.ne'] using hexp
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ w in 𝓝[≠] (0 : ℂ), (0 : ℝ) < ‖w‖ := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_pos_iff.mpr hw
  -- slice analyticity off `0`
  have hf : ∀ᶠ w in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun w => φ (z, w)) w := by
    filter_upwards [hlt, hpos] with w hw1 hw2
    exact AnalyticAt.comp (g := φ) (f := fun w => (z, w))
      (han z w hz hw2 hw1) (analyticAt_const.prod analyticAt_id)
  -- boundedness via the Cauchy root bound near `0`
  have hcons : Continuous (fun w : ℂ => (Fin.cons (w ^ m) z : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using continuous_pow m
    · simpa using continuous_const
  obtain ⟨ε, _, hεbd⟩ := roots_bound_eventually (fun w : ℂ => q (Fin.cons (w ^ m) z)) m 0
    (fun w => hmonic _) (fun w => hdeg _)
    (fun i => (Continuous.comp (hcoeff i) hcons).continuousAt)
  have hb : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖(fun w => φ (z, w)) w‖ ≤ ε := by
    filter_upwards [hlt, hpos, hεbd.filter_mono nhdsWithin_le_nhds] with w hw1 hw2 hwbd
    refine hwbd (φ (z, w)) ?_
    rw [Multiset.mem_toFinset, mem_roots (hmonic _).ne_zero]
    exact hroot z w hz hw2 hw1
  exact exists_analyticAt_extend_of_bdd hf hb

/-- Multiplication by a nonzero constant maps the punctured neighbourhood of `0` to itself. -/
theorem tendsto_const_mul_punctured {s : ℂ} (hs : s ≠ 0) :
    Filter.Tendsto (fun u : ℂ => s * u) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Filter.Tendsto (fun u : ℂ => s * u) (𝓝 (0 : ℂ)) (𝓝 (s * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero hs (Set.mem_compl_singleton_iff.mp hu))

/-- **Branch-difference is analytic on a full disc.** For two unit-modulus constants `a, b`, the
slice `u ↦ φ(z, a·u) − φ(z, b·u)` is analytic on `ball 0 R` (`Rᵐ < exp c`): away from `0` directly
from the slice-analyticity of `φ`, at `0` by the removable singularity (`exists_phi_slice_extend`)
since both branches share the limit of the extension `F` (so the difference vanishes at `0`). -/
theorem branchDiff_slice_analyticOnNhd {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z : Fin n → ℂ} (hz : ‖z‖ < δz) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {R : ℝ} (hRc : R ^ m < Real.exp c) :
    AnalyticOnNhd ℂ (fun u => φ (z, a * u) - φ (z, b * u)) (Metric.ball 0 R) := by
  have ha0 : a ≠ 0 := by rw [← norm_pos_iff, ha]; norm_num
  have hb0 : b ≠ 0 := by rw [← norm_pos_iff, hb]; norm_num
  intro u₀ hu₀
  rw [Metric.mem_ball, dist_zero_right] at hu₀
  rcases eq_or_ne u₀ 0 with rfl | hu₀ne
  · -- at `0`: use the analytic extension of the slice
    obtain ⟨F, hFan, hFeq⟩ := exists_phi_slice_extend hm hmonic hdeg hcoeff hroot han hz
    have hHan : AnalyticAt ℂ (fun u => F (a * u) - F (b * u)) 0 := by
      have h1 : AnalyticAt ℂ (fun u => F (a * u)) 0 :=
        AnalyticAt.comp (g := F) (f := fun u => a * u)
          (by simpa using hFan) (analyticAt_const.mul analyticAt_id)
      have h2 : AnalyticAt ℂ (fun u => F (b * u)) 0 :=
        AnalyticAt.comp (g := F) (f := fun u => b * u)
          (by simpa using hFan) (analyticAt_const.mul analyticAt_id)
      exact h1.sub h2
    have hEqa : ∀ᶠ u in 𝓝[≠] (0 : ℂ), F (a * u) = φ (z, a * u) :=
      (tendsto_const_mul_punctured ha0).eventually hFeq
    have hEqb : ∀ᶠ u in 𝓝[≠] (0 : ℂ), F (b * u) = φ (z, b * u) :=
      (tendsto_const_mul_punctured hb0).eventually hFeq
    have hpunc : (fun u => F (a * u) - F (b * u)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u => φ (z, a * u) - φ (z, b * u)) := by
      filter_upwards [hEqa, hEqb] with u e1 e2; rw [e1, e2]
    have hval : (fun u => F (a * u) - F (b * u)) 0 = (fun u => φ (z, a * u) - φ (z, b * u)) 0 := by
      simp
    exact hHan.congr (eventuallyEq_nhds_of_nhdsWithin_ne hpunc hval)
  · -- away from `0`: direct slice-analyticity of `φ`
    have hu0n : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
    have hnorm : ∀ s : ℂ, ‖s‖ = 1 → 0 < ‖s * u₀‖ ∧ ‖s * u₀‖ ^ m < Real.exp c := by
      intro s hs
      rw [norm_mul, hs, one_mul]
      exact ⟨hu0n, lt_trans (pow_lt_pow_left₀ hu₀ (norm_nonneg u₀) hm.ne') hRc⟩
    have h1 : AnalyticAt ℂ (fun u => φ (z, a * u)) u₀ :=
      AnalyticAt.comp (g := φ) (f := fun u => (z, a * u))
        (han z (a * u₀) hz (hnorm a ha).1 (hnorm a ha).2)
        (analyticAt_const.prod (analyticAt_const.mul analyticAt_id))
    have h2 : AnalyticAt ℂ (fun u => φ (z, b * u)) u₀ :=
      AnalyticAt.comp (g := φ) (f := fun u => (z, b * u))
        (han z (b * u₀) hz (hnorm b hb).1 (hnorm b hb).2)
        (analyticAt_const.prod (analyticAt_const.mul analyticAt_id))
    exact h1.sub h2

/-- **Branch-difference is jointly continuous off `u = 0`.** On `S ×ˢ {0 < ‖u‖ ∧ ‖u‖ᵐ < exp c}`
(with `S` inside the parametrization domain `‖z‖ < δz`), the branch difference `φ(z,a·u) − φ(z,b·u)`
is continuous, since `φ` is analytic (hence continuous) at each such point. -/
theorem branchDiff_continuousOn {n m : ℕ} {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {S : Set (Fin n → ℂ)}
    (hSsub : ∀ z ∈ S, ‖z‖ < δz) :
    ContinuousOn (Function.uncurry (fun z u => φ (z, a * u) - φ (z, b * u)))
      (S ×ˢ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c}) := by
  rintro ⟨z, u⟩ hp
  have hzδ : ‖z‖ < δz := hSsub z hp.1
  have hnorm : ∀ s : ℂ, ‖s‖ = 1 → 0 < ‖s * u‖ ∧ ‖s * u‖ ^ m < Real.exp c := by
    intro s hs; rw [norm_mul, hs, one_mul]; exact ⟨hp.2.1, hp.2.2⟩
  have hfa : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => (p.1, a * p.2)) (z, u) :=
    continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
  have hfb : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => (p.1, b * p.2)) (z, u) :=
    continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
  have c1 : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => φ (p.1, a * p.2)) (z, u) :=
    ContinuousAt.comp (g := φ) (f := fun p : (Fin n → ℂ) × ℂ => (p.1, a * p.2)) (x := (z, u))
      (han z (a * u) hzδ (hnorm a ha).1 (hnorm a ha).2).continuousAt hfa
  have c2 : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => φ (p.1, b * p.2)) (z, u) :=
    ContinuousAt.comp (g := φ) (f := fun p : (Fin n → ℂ) × ℂ => (p.1, b * p.2)) (x := (z, u))
      (han z (b * u) hzδ (hnorm b hb).1 (hnorm b hb).2).continuousAt hfb
  exact (c1.sub c2).continuousWithinAt

open Polynomial in
/-- **The Puiseux branches are distinct at a separable point.** At `u ≠ 0` (in the parametrization
domain) where `q(cons(uᵐ, z))` is separable, the map `i ↦ φ(z, ζⁱ·u)` is injective (the `m` branches
enumerate the `m` distinct roots). -/
theorem branches_injective {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} {u : ℂ}
    (hz : ‖z‖ < δz) (hu : 0 < ‖u‖) (hud : ‖u‖ ^ m < Real.exp c)
    (hsepu : (q (Fin.cons (u ^ m) z)).Separable) :
    Function.Injective (fun i : Fin m => φ (z, ζ ^ (i : ℕ) * u)) := by
  classical
  set p := q (Fin.cons (u ^ m) z) with hp
  set r : Fin m → ℂ := fun i => φ (z, ζ ^ (i : ℕ) * u) with hr
  have hpne : p ≠ 0 := (hmonic _).ne_zero
  have hpm : p.natDegree = m := hdeg _
  have hmem : ∀ x, x ∈ p.roots ↔ ∃ i : Fin m, r i = x := by
    intro x
    rw [mem_roots hpne, IsRoot.def, hiff z u x hz hu hud]
    constructor
    · rintro ⟨u', hu'm, hu'φ⟩
      obtain ⟨i, hi⟩ := (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mp hu'm
      exact ⟨i, by show φ (z, ζ ^ (i : ℕ) * u) = x; rw [← hi]; exact hu'φ⟩
    · rintro ⟨i, hi⟩
      exact ⟨ζ ^ (i : ℕ) * u, (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mpr ⟨i, rfl⟩, hi⟩
  have hrootcard : p.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepu),
      (splits_iff_card_roots.mp (IsAlgClosed.splits p)), hpm]
  have himg : Finset.image r Finset.univ = p.roots.toFinset := by
    ext x
    rw [Finset.mem_image, Multiset.mem_toFinset, hmem x]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩⟩
  rw [← Set.injOn_univ, ← Finset.coe_univ]
  refine Finset.injOn_of_card_image_eq ?_
  rw [himg, hrootcard, Finset.card_univ, Fintype.card_fin]

/-- **Branch-difference has finite order at `0`.** For `i ≠ j`, the difference `φ(z,ζⁱ·) − φ(z,ζʲ·)`
does not vanish identically near `0` (the branches are distinct off `0` by separability), so its
analytic order at `0` is finite. -/
theorem branchDiff_order_ne_top {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    (hsep_punc : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {i j : Fin m} (hij : i ≠ j) :
    analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  -- region near `0`
  have hreg : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖u‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun u : ℂ => ‖u‖ ^ m) 0 := (continuous_norm.pow m).continuousAt
    have h0 : (fun u : ℂ => ‖u‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using Real.exp_pos c
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  have hcontra : ∀ᶠ u in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [htop.filter_mono nhdsWithin_le_nhds, hsep_punc, hreg,
      self_mem_nhdsWithin] with u hu0 hsepu hudu huneq
    have hune : u ≠ 0 := huneq
    have hu : 0 < ‖u‖ := norm_pos_iff.mpr hune
    have hinj := branches_injective hm hmonic hdeg hiff hζ hz hu hudu hsepu
    exact hij (hinj (by simpa using sub_eq_zero.mp hu0))
  exact (NeBot.ne (by infer_instance) (Filter.eventually_false_iff_eq_bot.mp hcontra))

/-! ### Step B — order of the branch product equals the sum of branch-difference orders -/

/-- **Sum of branch-difference orders = order of the branch product.** With the off-diagonal
"branch difference" family `η_{ij} = φ(z,ζⁱ·) − φ(z,ζʲ·)` (and diagonal entries set to the unit `1`),
the sum over all pairs of the analytic orders equals the order of the full product
`∏ᵢ ∏_{j≠i} η_{ij}` (which is `±disc` by `weierstrass_disc_eq_prod_branches`). Diagonal entries
contribute `0`; the product splits by `analyticOrderAt_prod`. -/
theorem sum_order_eq_order_branchProd {n m : ℕ} {φ : (Fin n → ℂ) × ℂ → ℂ} {ζ : ℂ} {z : Fin n → ℂ}
    (hdiff_an : ∀ i j : Fin m, i ≠ j →
      AnalyticAt ℂ (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0) :
    (∑ k : Fin m × Fin m, analyticOrderAt
        (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = analyticOrderAt
        (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 := by
  classical
  -- RHS as a double sum via `analyticOrderAt_prod`
  have hRHS : analyticOrderAt
      (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
        (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
          analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 := by
    rw [analyticOrderAt_prod (Finset.univ : Finset (Fin m))
      (fun i => fun u => ∏ j ∈ Finset.univ.erase i,
        (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)))
      (fun i _ => Finset.analyticAt_fun_prod _
        (fun j hj => hdiff_an i j ((Finset.mem_erase.mp hj).1).symm))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact analyticOrderAt_prod (Finset.univ.erase i)
      (fun j => fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))
      (fun j hj => hdiff_an i j ((Finset.mem_erase.mp hj).1).symm)
  -- LHS as the same double sum: diagonal terms vanish
  rw [hRHS, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  have hc : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 0 = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  rw [hc, zero_add]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [if_neg (Ne.symm hji)]

/-! ### Bridge ingredient — the discriminant equals the branch product near `u = 0` -/

open Polynomial in
/-- **Discriminant = branch product on the punctured disc.** For fixed `z` in the domain, where
`q(cons(uᵐ, z))` is separable for small `u ≠ 0`, the discriminant `u ↦ disc(q(cons(uᵐ, z)))` agrees
with `±` the branch product `∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` on a punctured neighbourhood of `0`
(pointwise `weierstrass_disc_eq_prod_branches`). This is the analytic identity feeding the bridge:
the order of the branch product (Step B) equals the order of the discriminant, which the discriminant
theory controls. -/
theorem disc_eventuallyEq_branchProd {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    (hsep : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable) :
    (fun u => (q (Fin.cons (u ^ m) z)).discr) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun u => (-1) ^ (m * (m - 1) / 2)
        * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) := by
  have hlt : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖u‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun u : ℂ => ‖u‖ ^ m) 0 := (continuous_norm.pow m).continuousAt
    have h0 : (fun u : ℂ => ‖u‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using Real.exp_pos c
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsep, hlt, self_mem_nhdsWithin] with u hsepu hudu huneq
  have hune : u ≠ 0 := huneq
  exact weierstrass_disc_eq_prod_branches hm hmonic hdeg hiff hζ hz (norm_pos_iff.mpr hune) hudu hsepu

/-! ### Assembly — branch-difference orders are locally constant (modulo the bridge) -/

/-- **Lemma 4.2.7 (branch-order constancy), assembled.** Given the Newton–Puiseux parametrization
data for a Weierstrass family `q` and a base point `z₀` in the domain, with the branch points
`ζⁱ·u`, IF the order of the branch product `∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` (which is `±disc`) is
locally constant in `z` (the *bridge* hypothesis, supplied by the discriminant theory), THEN each
branch-difference order is locally constant. This combines Step A (`branchDiff_*`,
`branchDiff_order_ne_top`), Step B (`sum_order_eq_order_branchProd`), and the abstract heart
`branch_order_constant`. -/
theorem branchDiff_orders_eventually_constant {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z₀ : Fin n → ℂ} (hz₀ : ‖z₀‖ < δz)
    (hsep₀ : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z₀)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hbridge : ∀ᶠ z in 𝓝 z₀,
        analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u))) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt (fun u => φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u)) 0 := by
  classical
  have hnormζ : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
  have hnormζp : ∀ i : Fin m, ‖ζ ^ (i : ℕ)‖ = 1 := fun i => by rw [norm_pow, hnormζ, one_pow]
  have hR : 0 < R := lt_trans hρ hρR
  -- a neighbourhood of `z₀` inside the domain
  have hrz : 0 < δz - ‖z₀‖ := by linarith
  have hS : Metric.ball z₀ (δz - ‖z₀‖) ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ hrz
  have hSsub : ∀ z ∈ Metric.ball z₀ (δz - ‖z₀‖), ‖z‖ < δz := by
    intro z hz
    have hd : dist z z₀ < δz - ‖z₀‖ := Metric.mem_ball.mp hz
    have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by simpa using norm_add_le z₀ (z - z₀)
    rw [dist_eq_norm] at hd; linarith
  have hzev : ∀ᶠ z in 𝓝 z₀, ‖z‖ < δz := Filter.eventually_of_mem hS hSsub
  -- the contour radius lies in the punctured `u`-domain
  have hTc : ∀ θ : ℝ, circleMap 0 ρ θ ∈ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c} := by
    intro θ
    rw [Set.mem_setOf_eq, norm_circleMap_zero, abs_of_pos hρ]
    exact ⟨hρ, lt_trans (pow_lt_pow_left₀ hρR hρ.le hm.ne') hRc⟩
  -- per-slice analyticity of branch differences (Step A)
  have hdiff_an : ∀ z, ‖z‖ < δz → ∀ i j : Fin m, i ≠ j →
      AnalyticAt ℂ (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 := by
    intro z hz i j _
    exact branchDiff_slice_analyticOnNhd hm hmonic hdeg hcoeff hroot han hz
      (hnormζp i) (hnormζp j) hRc 0 (Metric.mem_ball_self hR)
  -- Step B: the pair-sum of orders equals the order of the branch product
  have hsum_at : ∀ z, ‖z‖ < δz →
      (∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 :=
    fun z hz => sum_order_eq_order_branchProd (fun i j hij => hdiff_an z hz i j hij)
  -- the hypotheses of `branch_order_constant`
  have hcont : ∀ k : Fin m × Fin m, ContinuousOn (Function.uncurry
      (fun (z : Fin n → ℂ) (u : ℂ) => if k.1 = k.2 then (1 : ℂ)
        else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)))
      (Metric.ball z₀ (δz - ‖z₀‖) ×ˢ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c}) := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · simp only [if_pos h]; exact continuousOn_const
    · simp only [if_neg h]
      exact branchDiff_continuousOn han (hnormζp k.1) (hnormζp k.2) hSsub
  have hana : ∀ k : Fin m × Fin m, ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ
      (fun u => if k.1 = k.2 then (1 : ℂ)
        else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) (Metric.ball 0 R) := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · filter_upwards with z; simp only [if_pos h]; exact analyticOnNhd_const
    · filter_upwards [hzev] with z hz; simp only [if_neg h]
      exact branchDiff_slice_analyticOnNhd hm hmonic hdeg hcoeff hroot han hz
        (hnormζp k.1) (hnormζp k.2) hRc
  have hfin : ∀ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
      else φ (z₀, ζ ^ (k.1 : ℕ) * u) - φ (z₀, ζ ^ (k.2 : ℕ) * u)) 0 ≠ ⊤ := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · simp only [if_pos h]
      have h0 : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 0 = 0 :=
        analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
      rw [h0]; exact (by decide)
    · simp only [if_neg h]
      exact branchDiff_order_ne_top hm hmonic hdeg hiff hζ hz₀ hsep₀ h
  have hbp0 := hsum_at z₀ hz₀
  have hsumconst : ∀ᶠ z in 𝓝 z₀,
      (∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = ∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z₀, ζ ^ (k.1 : ℕ) * u) - φ (z₀, ζ ^ (k.2 : ℕ) * u)) 0 := by
    filter_upwards [hbridge, hzev] with z hbz hz
    rw [hsum_at z hz, hbz, ← hbp0]
  have key := branch_order_constant (η := fun (k : Fin m × Fin m) (z : Fin n → ℂ) (u : ℂ) =>
      if k.1 = k.2 then (1 : ℂ) else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u))
      (z₀ := z₀) (S := Metric.ball z₀ (δz - ‖z₀‖))
      (T := {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c})
      hS hρ hρR hTc hcont hana hfin hsumconst
  filter_upwards [key] with z hz
  intro i j hij
  have h := hz (i, j)
  simp only [if_neg hij] at h
  exact h

end Puiseux
