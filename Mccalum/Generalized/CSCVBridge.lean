import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mccalum.Generalized.CParamIntegral

/-!
# Several-complex-variables bridge — Step 4 build (WIP)

This file builds the missing several-complex-variables infrastructure needed to discharge `osgood`
(equivalently, the bridge `jointly ℂ-differentiable ⇒ analytic` on `ℂⁿ`). Per `CBridge.lean`, the
polydisc–Cauchy route is proved through the iterated/torus Cauchy representation (`bridge_torus_repr`);
what remains ("Step 4") is to **expand the Cauchy kernel into a several-variable power series** and
package it as a `HasFPowerSeriesOnBall` on `ℂ²` (then `ℂⁿ`).

Foundation stone: the **Cauchy-kernel geometric expansion** `(ζ − z)⁻¹ = ∑_j (z−z₀)^j/(ζ−z₀)^{j+1}`
for `‖z − z₀‖ < ‖ζ − z₀‖`. This is the 1-variable analytic engine; the several-variable kernel is its
(two-fold) product, integrated term-by-term over the torus.
-/

noncomputable section

open Complex Metric
open scoped Real

/-- **Cauchy-kernel geometric expansion.** For `‖z − z₀‖ < ‖ζ − z₀‖`,
`∑_j (z−z₀)^j / (ζ−z₀)^{j+1} = (ζ − z)⁻¹` (a `HasSum`). The summand is the `z`-power-series coefficient
of the Cauchy kernel; this is the engine that turns the Cauchy integral into a power series. -/
theorem hasSum_cauchy_kernel {z₀ z ζ : ℂ} (h : ‖z - z₀‖ < ‖ζ - z₀‖) :
    HasSum (fun j : ℕ => (z - z₀) ^ j / (ζ - z₀) ^ (j + 1)) ((ζ - z)⁻¹) := by
  have hζ0 : ζ - z₀ ≠ 0 := fun h0 => absurd h (by rw [h0, norm_zero]; exact not_lt.mpr (norm_nonneg _))
  have hζ0pos : 0 < ‖ζ - z₀‖ := norm_pos_iff.mpr hζ0
  have hζz : ζ - z ≠ 0 := fun h0 => by rw [sub_eq_zero] at h0; rw [h0] at h; exact lt_irrefl _ h
  have hq : ‖(z - z₀) / (ζ - z₀)‖ < 1 := by rw [norm_div]; exact (div_lt_one hζ0pos).mpr h
  have hmul := (hasSum_geometric_of_norm_lt_one hq).mul_right (ζ - z₀)⁻¹
  have hf : (fun j : ℕ => (z - z₀) ^ j / (ζ - z₀) ^ (j + 1))
      = fun j : ℕ => ((z - z₀) / (ζ - z₀)) ^ j * (ζ - z₀)⁻¹ := by
    funext j; rw [div_pow, pow_succ, div_mul_eq_div_div, div_eq_mul_inv]
  have hs : (ζ - z)⁻¹ = (1 - (z - z₀) / (ζ - z₀))⁻¹ * (ζ - z₀)⁻¹ := by
    have h1q : 1 - (z - z₀) / (ζ - z₀) = (ζ - z) / (ζ - z₀) := by field_simp; ring
    rw [h1q, inv_div]; field_simp
  rw [hf, hs]; exact hmul

/-- The Cauchy-kernel series is **absolutely** summable (geometric). -/
theorem summable_norm_cauchy_kernel {z₀ z ζ : ℂ} (h : ‖z - z₀‖ < ‖ζ - z₀‖) :
    Summable (fun j : ℕ => ‖(z - z₀) ^ j / (ζ - z₀) ^ (j + 1)‖) := by
  have hζ0 : ζ - z₀ ≠ 0 := fun h0 => absurd h (by rw [h0, norm_zero]; exact not_lt.mpr (norm_nonneg _))
  have hq : ‖z - z₀‖ / ‖ζ - z₀‖ < 1 := (div_lt_one (norm_pos_iff.mpr hζ0)).mpr h
  have heq : (fun j : ℕ => ‖(z - z₀) ^ j / (ζ - z₀) ^ (j + 1)‖)
      = fun j : ℕ => (‖z - z₀‖ / ‖ζ - z₀‖) ^ j * ‖ζ - z₀‖⁻¹ := by
    funext j
    rw [norm_div, norm_pow, norm_pow, div_pow, pow_succ, div_mul_eq_div_div, div_eq_mul_inv]
  rw [heq]
  exact (summable_geometric_of_lt_one (by positivity) hq).mul_right _

/-- **Two-variable Cauchy-kernel expansion.** For `(z,w)` inside the polydisc and `(ζ,η)` on the torus
(`‖z−z₀‖ < ‖ζ−z₀‖`, `‖w−w₀‖ < ‖η−w₀‖`), the product kernel `(ζ−z)⁻¹·(η−w)⁻¹` expands as the double
power series `∑_{(j,k)} (z−z₀)^j(w−w₀)^k / ((ζ−z₀)^{j+1}(η−w₀)^{k+1})` — a `HasSum` over `ℕ × ℕ` (the
absolutely-convergent product of the two one-variable kernels). -/
theorem hasSum_cauchy_kernel_two {z₀ z ζ w₀ w η : ℂ}
    (hz : ‖z - z₀‖ < ‖ζ - z₀‖) (hw : ‖w - w₀‖ < ‖η - w₀‖) :
    HasSum (fun jk : ℕ × ℕ => (z - z₀) ^ jk.1 * (w - w₀) ^ jk.2 /
        ((ζ - z₀) ^ (jk.1 + 1) * (η - w₀) ^ (jk.2 + 1)))
      ((ζ - z)⁻¹ * (η - w)⁻¹) := by
  have hfn := summable_norm_cauchy_kernel hz
  have hgn := summable_norm_cauchy_kernel hw
  have hprod : HasSum (fun x : ℕ × ℕ =>
      (z - z₀) ^ x.1 / (ζ - z₀) ^ (x.1 + 1) * ((w - w₀) ^ x.2 / (η - w₀) ^ (x.2 + 1)))
      ((ζ - z)⁻¹ * (η - w)⁻¹) := by
    rw [← (hasSum_cauchy_kernel hz).tsum_eq, ← (hasSum_cauchy_kernel hw).tsum_eq,
      tsum_mul_tsum_of_summable_norm hfn hgn]
    exact (summable_mul_of_summable_norm hfn hgn).hasSum
  have hfeq : (fun jk : ℕ × ℕ => (z - z₀) ^ jk.1 * (w - w₀) ^ jk.2 /
        ((ζ - z₀) ^ (jk.1 + 1) * (η - w₀) ^ (jk.2 + 1)))
      = fun x : ℕ × ℕ =>
        (z - z₀) ^ x.1 / (ζ - z₀) ^ (x.1 + 1) * ((w - w₀) ^ x.2 / (η - w₀) ^ (x.2 + 1)) := by
    funext jk; rw [div_mul_div_comm]
  rw [hfeq]; exact hprod

/-- **Step 3 (one variable): the Cauchy integral expands as a power series with explicit integral
coefficients.** For a slice `g = f(·, w)` holomorphic on the closed disc `|ζ − z₀| ≤ r`,
`2πi · f(z,w) = ∑_j ∮_ζ ((z−z₀)/(ζ−z₀))^j·(ζ−z₀)⁻¹·f(ζ,w)` for `‖z−z₀‖ < r`. This is Mathlib's
`hasSum_two_pi_I_cauchyPowerSeries_integral` (the 1-var integral–sum swap, done by dominated
convergence) combined with the Cauchy integral formula for the value. -/
theorem hasSum_z_expansion {f : ℂ × ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {w : ℂ}
    (hcont : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ r))
    (hdiff : ∀ ζ ∈ ball z₀ r, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ)
    {z : ℂ} (hz : ‖z - z₀‖ < r) :
    HasSum (fun j : ℕ => ∮ ζ in C(z₀, r), ((z - z₀) / (ζ - z₀)) ^ j • (ζ - z₀)⁻¹ • f (ζ, w))
      ((2 * π * I : ℂ) • f (z, w)) := by
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hz
  have hci : CircleIntegrable (fun ζ => f (ζ, w)) z₀ r :=
    (hcont.mono sphere_subset_closedBall).circleIntegrable hrpos.le
  have hzmem : z ∈ ball z₀ r := mem_ball_iff_norm.mpr hz
  have hsum := hasSum_two_pi_I_cauchyPowerSeries_integral
    (f := fun ζ => f (ζ, w)) (c := z₀) (R := r) (w := z - z₀) hci hz
  rw [show z₀ + (z - z₀) = z from by ring,
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty hzmem hcont
      (fun ζ hζ => hdiff ζ hζ.1)] at hsum
  exact hsum

/-! ## Step 4: packaging into a `FormalMultilinearSeries` on `ℂ²`

The double-indexed Cauchy coefficients `c j k` are packaged into a several-variable power series. The
`n`-th term is `∑_{j+k=n} c_{jk}·mⱼ`, where `mⱼ` is the (asymmetric) monomial multilinear map reading
the first `j` slots' coordinate `1` and the rest's coordinate `2`. Its diagonal value is
`mⱼ(y,…,y) = y.1^j·y.2^{n-j}` — **no binomial coefficient**, which is what makes this construction
work. -/

open ContinuousMultilinearMap in
/-- The `n`-th term of the SCV power series built from coefficients `c : ℕ → ℕ → ℂ`. -/
def scvTerm (c : ℕ → ℕ → ℂ) (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ :=
  ∑ j ∈ Finset.range (n + 1), c j (n - j) •
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
      fun i => if (i : ℕ) < j then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ

/-- Helper: a constant-`ite` product over `range n` is `a^j · b^{n-j}` (for `j ≤ n`). -/
theorem prod_range_ite (a b : ℂ) {j n : ℕ} (hj : j ≤ n) :
    ∏ k ∈ Finset.range n, (if k < j then a else b) = a ^ j * b ^ (n - j) := by
  rw [← Finset.prod_range_mul_prod_Ico (fun k => if k < j then a else b) hj]
  congr 1
  · rw [Finset.prod_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk), Finset.prod_const,
      Finset.card_range]
  · rw [Finset.prod_congr rfl fun k hk => if_neg (by simp only [Finset.mem_Ico] at hk; omega),
      Finset.prod_const, Nat.card_Ico]

/-- **Diagonal evaluation of the SCV term:** `scvTerm c n (y,…,y) = ∑_{j+k=n} c_{jk}·y.1^j·y.2^{n-j}`.
This is the degree-`n` homogeneous part of the double power series — exactly what
`HasFPowerSeriesOnBall` needs on the diagonal. -/
theorem scvTerm_apply_diag (c : ℕ → ℕ → ℂ) (n : ℕ) (y : ℂ × ℂ) :
    scvTerm c n (fun _ => y) = ∑ j ∈ Finset.range (n + 1), c j (n - j) * (y.1 ^ j * y.2 ^ (n - j)) := by
  rw [scvTerm, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn, smul_eq_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range fun i => (if i < j then ContinuousLinearMap.fst ℂ ℂ ℂ
    else ContinuousLinearMap.snd ℂ ℂ ℂ) y]
  rw [Finset.prod_congr rfl fun k _ => by rw [apply_ite (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L y)]]
  exact prod_range_ite y.1 y.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- **Clean `z`-expansion** (coefficients pulled out of the integral): for a holomorphic `z`-slice,
`2πi·f(z,w) = ∑_j (z−z₀)^j · B_j(w)` with `B_j(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)`. This is the form that
combines with the `w`-expansion of each coefficient `B_j` (analytic in `w`) toward the double series. -/
theorem hasSum_z_expansion' {f : ℂ × ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hcont : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ r))
    (hdiff : ∀ ζ ∈ ball z₀ r, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ)
    {z : ℂ} (hz : ‖z - z₀‖ < r) :
    HasSum (fun j : ℕ => (z - z₀) ^ j • ∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      ((2 * π * I : ℂ) • f (z, w)) := by
  have hbase := hasSum_z_expansion hcont hdiff hz
  have hfeq : (fun j : ℕ => (z - z₀) ^ j • ∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      = fun j : ℕ => ∮ ζ in C(z₀, r), ((z - z₀) / (ζ - z₀)) ^ j • (ζ - z₀)⁻¹ • f (ζ, w) := by
    funext j
    rw [← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    have hζ0 : ζ - z₀ ≠ 0 := by
      rw [mem_sphere_iff_norm] at hζ
      intro h; rw [h, norm_zero] at hζ; exact (ne_of_lt hr) hζ
    simp only [smul_eq_mul]; rw [div_pow, pow_succ, mul_inv]; ring
  rw [hfeq]; exact hbase

open Finset in
/-- **Step 4 (b): regroup an `ℕ × ℕ` monomial `HasSum` by total degree.** From
`HasSum (fun (j,k) => c_{jk}·y.1^j·y.2^k) S` we get `HasSum (fun n => ∑_{j+k=n} c_{jk}·y.1^j·y.2^{n-j}) S`,
the degree-`n` homogeneous parts — matching `scvTerm_apply_diag`. Pure `HasSum` algebra (regroup over
`Finset.antidiagonal`). -/
theorem hasSum_graded {c : ℕ → ℕ → ℂ} {S : ℂ} (y : ℂ × ℂ)
    (h : HasSum (fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) S) :
    HasSum (fun n => ∑ j ∈ Finset.range (n + 1), c j (n - j) * (y.1 ^ j * y.2 ^ (n - j))) S := by
  have hσ : HasSum ((fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) ∘
      Finset.sigmaAntidiagonalEquivProd) S :=
    Finset.sigmaAntidiagonalEquivProd.hasSum_iff.mpr h
  have hsig := hσ.sigma fun n => hasSum_fintype fun x : ↥(Finset.antidiagonal n) =>
    ((fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) ∘
      Finset.sigmaAntidiagonalEquivProd) ⟨n, x⟩
  have hfeq : (fun n => ∑ x : ↥(Finset.antidiagonal n),
        ((fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) ∘
          Finset.sigmaAntidiagonalEquivProd) ⟨n, x⟩)
      = fun n => ∑ j ∈ Finset.range (n + 1), c j (n - j) * (y.1 ^ j * y.2 ^ (n - j)) := by
    funext n
    simp only [Function.comp_apply, Finset.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal n)
        fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hfeq] at hsig
  exact hsig

/-- **(a) differentiate-under-integral for the `z`-coefficient `B_j`.** Given `f` and its `w`-partial
`fw = ∂_w f` jointly continuous on `closedBall w₀ δ × sphere z₀ r`, and the slice `w ↦ f(ζ,w)` has
derivative `fw(ζ,w)`, the coefficient `B_j(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)` is differentiable in `w`,
with derivative obtained by differentiating under the integral. (Uses `circleIntegral_hasDerivAt`.) -/
theorem Bj_hasDerivAt {f fw : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (j : ℕ)
    (hf : ContinuousOn (fun p : ℂ × ℂ => f (p.2, p.1)) (closedBall w₀ δ ×ˢ sphere z₀ r))
    (hfw : ContinuousOn (fun p : ℂ × ℂ => fw (p.2, p.1)) (closedBall w₀ δ ×ˢ sphere z₀ r))
    (hderiv : ∀ w ∈ ball w₀ δ, ∀ ζ ∈ sphere z₀ r,
      HasDerivAt (fun w' => f (ζ, w')) (fw (ζ, w)) w) :
    HasDerivAt (fun w => ∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      (∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • fw (ζ, w₀)) w₀ := by
  -- the polynomial factor is continuous and nonvanishing on `sphere z₀ r`
  have hfac : ContinuousOn (fun p : ℂ × ℂ => ((p.2 - z₀) ^ (j + 1))⁻¹)
      (closedBall w₀ δ ×ˢ sphere z₀ r) := by
    refine ContinuousOn.inv₀ ((continuous_snd.sub continuous_const).pow _).continuousOn ?_
    rintro ⟨w, ζ⟩ ⟨-, hζ⟩
    rw [mem_sphere_iff_norm] at hζ
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro h; rw [h, sub_self, norm_zero] at hζ; exact (ne_of_lt hr) hζ
  exact circleIntegral_hasDerivAt (Φ := fun w ζ => ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
    (Φ' := fun w ζ => ((ζ - z₀) ^ (j + 1))⁻¹ • fw (ζ, w)) hδ hr.le (hfac.smul hf) (hfac.smul hfw)
    fun w hw ζ hζ => (hderiv w hw ζ hζ).const_smul ((ζ - z₀) ^ (j + 1))⁻¹

/-- **(c) diagonal HasSum.** The `n`-th-degree HasSum that `HasFPowerSeriesOnBall` needs on the
diagonal: from the `ℕ×ℕ` monomial HasSum `∑_{j,k} c_{jk}·y.1^j·y.2^k = S`, the series of homogeneous
parts `∑_n scvTerm c n (y,…,y) = S`. (Combines `scvTerm_apply_diag` with `hasSum_graded`.) -/
theorem hasSum_scvTerm_diag {c : ℕ → ℕ → ℂ} {S : ℂ} (y : ℂ × ℂ)
    (h : HasSum (fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) S) :
    HasSum (fun n => scvTerm c n fun _ => y) S := by
  simp only [scvTerm_apply_diag]
  exact hasSum_graded y h

end
