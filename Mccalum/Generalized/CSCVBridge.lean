import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
open scoped Real Topology




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


/-- **(c) diagonal HasSum.** The `n`-th-degree HasSum that `HasFPowerSeriesOnBall` needs on the
diagonal: from the `ℕ×ℕ` monomial HasSum `∑_{j,k} c_{jk}·y.1^j·y.2^k = S`, the series of homogeneous
parts `∑_n scvTerm c n (y,…,y) = S`. (Combines `scvTerm_apply_diag` with `hasSum_graded`.) -/
theorem hasSum_scvTerm_diag {c : ℕ → ℕ → ℂ} {S : ℂ} (y : ℂ × ℂ)
    (h : HasSum (fun jk : ℕ × ℕ => c jk.1 jk.2 * (y.1 ^ jk.1 * y.2 ^ jk.2)) S) :
    HasSum (fun n => scvTerm c n fun _ => y) S := by
  simp only [scvTerm_apply_diag]
  exact hasSum_graded y h

/-- **Operator-norm bound on the SCV term:** `‖scvTerm c n‖ ≤ ∑_{j+k=n} ‖c_{jk}‖` (each monomial
multilinear map has norm `≤ 1`). The input for bounding the radius of convergence. -/
theorem norm_scvTerm_le (c : ℕ → ℕ → ℂ) (n : ℕ) :
    ‖scvTerm c n‖ ≤ ∑ j ∈ Finset.range (n + 1), ‖c j (n - j)‖ := by
  rw [scvTerm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  have hm : ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
      fun i => if (i : ℕ) < j then ContinuousLinearMap.fst ℂ ℂ ℂ
        else ContinuousLinearMap.snd ℂ ℂ ℂ‖ ≤ 1 := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖ ≤ 1 :=
      ContinuousMultilinearMap.norm_mkPiAlgebraFin_le.trans (by rw [norm_one, max_self])
    refine mul_le_one₀ hmk
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
      (Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_)
    split_ifs
    · exact ContinuousLinearMap.norm_fst_le ..
    · exact ContinuousLinearMap.norm_snd_le ..
  calc ‖c j (n - j)‖ * ‖_‖ ≤ ‖c j (n - j)‖ * 1 := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = ‖c j (n - j)‖ := mul_one _

/-- The several-variable power series whose `n`-th term is `scvTerm c n`. -/
def scvSeries (c : ℕ → ℕ → ℂ) : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ := fun n => scvTerm c n

/-- **Radius bound from a Cauchy coefficient bound.** If the coefficients satisfy the polydisc
Cauchy estimate `‖c_{jk}‖ ≤ M / ρ^{j+k}`, then any `s < ρ` is below the radius of convergence of
`scvSeries c`. (The `(n+1)` degeneracy factor from `norm_scvTerm_le` is absorbed by summability of
`(n+1) tⁿ` for `t = s/ρ < 1`.) -/
theorem le_radius_scvSeries {c : ℕ → ℕ → ℂ} {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hc : ∀ j k, ‖c j k‖ ≤ M / ρ ^ (j + k)) {s : NNReal} (hs : (s : ℝ) < ρ) :
    (s : ENNReal) ≤ (scvSeries c).radius := by
  set t : ℝ := (s : ℝ) / ρ with ht_def
  have ht0 : 0 ≤ t := div_nonneg s.2 hρ.le
  have ht1 : t < 1 := (div_lt_one hρ).mpr hs
  -- Summability of the comparison majorant `(n+1) · M · tⁿ`.
  have hgsum : Summable (fun n : ℕ => ((n : ℝ) + 1) * M * t ^ n) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) * t ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := t)
        (by rwa [Real.norm_eq_abs, abs_of_nonneg ht0])
    have h2 : Summable (fun n : ℕ => t ^ n) := summable_geometric_of_lt_one ht0 ht1
    refine ((h1.add h2).mul_left M).congr fun n => ?_
    ring
  apply (scvSeries c).le_radius_of_summable
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgsum
  -- `‖scvSeries c n‖ · sⁿ ≤ (n+1) · M · tⁿ`.
  have hjn : ‖scvSeries c n‖ ≤ ((n : ℝ) + 1) * M / ρ ^ n := by
    calc ‖scvSeries c n‖ ≤ ∑ j ∈ Finset.range (n + 1), ‖c j (n - j)‖ := norm_scvTerm_le c n
      _ ≤ ∑ _j ∈ Finset.range (n + 1), M / ρ ^ n := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          calc ‖c j (n - j)‖ ≤ M / ρ ^ (j + (n - j)) := hc j (n - j)
            _ = M / ρ ^ n := by rw [Nat.add_sub_cancel' hjle]
      _ = ((n : ℝ) + 1) * M / ρ ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  calc ‖scvSeries c n‖ * (s : ℝ) ^ n
      ≤ (((n : ℝ) + 1) * M / ρ ^ n) * (s : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hjn (by positivity)
    _ = ((n : ℝ) + 1) * M * t ^ n := by rw [ht_def, div_pow]; ring

/-- `‖2πI‖ = 2π`. -/
theorem norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [show (2 * π * I : ℂ) = ((2 * π : ℝ) : ℂ) * I by push_cast; ring, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The torus Cauchy coefficient `c_{jk} = (2πI)⁻² ∮_η (η-w₀)^{-(k+1)} ∮_ζ (ζ-z₀)^{-(j+1)} f(ζ,η)`. -/
noncomputable def scvCoeff (f : ℂ × ℂ → ℂ) (z₀ w₀ : ℂ) (rz rw : ℝ) (j k : ℕ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), ((η - w₀) ^ (k + 1))⁻¹ •
    (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)

/-- **Nested Cauchy estimate:** if `‖f‖ ≤ M` on the torus, then `‖c_{jk}‖ ≤ M / (rz^j · rw^k)`. -/
theorem norm_scvCoeff_le {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw M : ℝ}
    (hrz : 0 < rz) (hrw : 0 < rw)
    (hb : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ sphere w₀ rw, ‖f (ζ, η)‖ ≤ M) (j k : ℕ) :
    ‖scvCoeff f z₀ w₀ rz rw j k‖ ≤ M / (rz ^ j * rw ^ k) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hb (z₀ + rz) (by simp [mem_sphere_iff_norm, abs_of_pos hrz])
      (w₀ + rw) (by simp [mem_sphere_iff_norm, abs_of_pos hrw]))
  have hnorminv : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by rw [norm_inv, norm_two_pi_I]
  -- Uniform bound on the inner `(2πI)⁻¹ • ∮_ζ …` over `η` on the `w`-sphere.
  have hinner : ∀ η ∈ sphere w₀ rw,
      ‖(2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)‖
        ≤ M / rz ^ j := by
    intro η hη
    have hI : ‖∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)‖
        ≤ 2 * π * rz * (M / rz ^ (j + 1)) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const hrz.le fun ζ hζ => ?_
      have hζn : ‖ζ - z₀‖ = rz := mem_sphere_iff_norm.mp hζ
      rw [norm_smul, norm_inv, norm_pow, hζn, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hb ζ hζ η hη) (by positivity)
    rw [norm_smul, hnorminv]
    calc (2 * π)⁻¹ * ‖∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)‖
        ≤ (2 * π)⁻¹ * (2 * π * rz * (M / rz ^ (j + 1))) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = M / rz ^ j := by
          rw [pow_succ]; field_simp
  -- Outer integral bound.
  have hO : ‖∮ η in C(w₀, rw), ((η - w₀) ^ (k + 1))⁻¹ •
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)‖
        ≤ 2 * π * rw * ((M / rz ^ j) / rw ^ (k + 1)) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hrw.le fun η hη => ?_
    have hηn : ‖η - w₀‖ = rw := mem_sphere_iff_norm.mp hη
    rw [norm_smul, norm_inv, norm_pow, hηn, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hinner η hη) (by positivity)
  rw [scvCoeff, norm_smul, hnorminv]
  calc (2 * π)⁻¹ * ‖∮ η in C(w₀, rw), ((η - w₀) ^ (k + 1))⁻¹ •
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, η)‖
      ≤ (2 * π)⁻¹ * (2 * π * rw * ((M / rz ^ j) / rw ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hO (by positivity)
    _ = M / (rz ^ j * rw ^ k) := by rw [pow_succ]; field_simp

/-- **Summability of the double coefficient family** on the open polydisc: from the Cauchy bound
`‖c_{jk}‖ ≤ M/(rz^j·rw^k)` and `‖z-z₀‖<rz`, `‖w-w₀‖<rw`, the family
`c_{jk}·(z−z₀)^j(w−w₀)^k` is summable over `ℕ×ℕ` (dominated by a product of two geometrics). -/
theorem summable_scvCoeff_family {f : ℂ × ℂ → ℂ} {z₀ w₀ z w : ℂ} {rz rw M : ℝ}
    (hrz : 0 < rz) (hrw : 0 < rw)
    (hb : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ sphere w₀ rw, ‖f (ζ, η)‖ ≤ M)
    (hz : ‖z - z₀‖ < rz) (hw : ‖w - w₀‖ < rw) :
    Summable (fun jk : ℕ × ℕ => scvCoeff f z₀ w₀ rz rw jk.1 jk.2 *
      ((z - z₀) ^ jk.1 * (w - w₀) ^ jk.2)) := by
  set a := ‖z - z₀‖ / rz with ha_def
  set b := ‖w - w₀‖ / rw with hb_def
  have ha0 : 0 ≤ a := div_nonneg (norm_nonneg _) hrz.le
  have hb0 : 0 ≤ b := div_nonneg (norm_nonneg _) hrw.le
  have ha1 : a < 1 := (div_lt_one hrz).mpr hz
  have hb1 : b < 1 := (div_lt_one hrw).mpr hw
  have hmaj : Summable (fun jk : ℕ × ℕ => M * (a ^ jk.1 * b ^ jk.2)) :=
    ((Summable.mul_of_nonneg (summable_geometric_of_lt_one ha0 ha1)
      (summable_geometric_of_lt_one hb0 hb1) (fun n => pow_nonneg ha0 n)
      fun n => pow_nonneg hb0 n)).mul_left M
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun jk => norm_nonneg _) (fun jk => ?_) hmaj)
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖scvCoeff f z₀ w₀ rz rw jk.1 jk.2‖ * (‖z - z₀‖ ^ jk.1 * ‖w - w₀‖ ^ jk.2)
      ≤ (M / (rz ^ jk.1 * rw ^ jk.2)) * (‖z - z₀‖ ^ jk.1 * ‖w - w₀‖ ^ jk.2) :=
        mul_le_mul_of_nonneg_right (norm_scvCoeff_le hrz hrw hb jk.1 jk.2) (by positivity)
    _ = M * (a ^ jk.1 * b ^ jk.2) := by rw [ha_def, hb_def, div_pow, div_pow]; field_simp

/-- **One-variable Cauchy power-series expansion**, obtained from `hasSum_z_expansion'` by ignoring
the first coordinate (`f := fun p => g p.1`). -/
theorem hasSum_w_expansion {g : ℂ → ℂ} {w₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn g (closedBall w₀ r))
    (hdiff : ∀ η ∈ ball w₀ r, DifferentiableAt ℂ g η)
    {w : ℂ} (hw : ‖w - w₀‖ < r) :
    HasSum (fun k : ℕ => (w - w₀) ^ k • ∮ η in C(w₀, r), ((η - w₀) ^ (k + 1))⁻¹ • g η)
      ((2 * π * I : ℂ) • g w) :=
  hasSum_z_expansion' (f := fun p : ℂ × ℂ => g p.1) (w := w₀) hr hcont hdiff hw

/-- **Parametric continuity of a circle integral over an arbitrary parameter set.** If the integrand
`Φ w ζ` is jointly continuous on `s ×ˢ sphere z₀ r`, then `w ↦ ∮_ζ Φ w ζ` is continuous on `s`.
(Via `continuous_parametric_intervalIntegral_of_continuous'` on the parameter subtype.) -/
theorem circleIntegral_continuousOn_param {X : Type*} [TopologicalSpace X] {Φ : X → ℂ → ℂ}
    {z₀ : ℂ} {r : ℝ} {s : Set X} (hr : 0 ≤ r)
    (hΦ : ContinuousOn (fun p : X × ℂ => Φ p.1 p.2) (s ×ˢ sphere z₀ r)) :
    ContinuousOn (fun w => ∮ ζ in C(z₀, r), Φ w ζ) s := by
  rw [continuousOn_iff_continuous_restrict]
  simp only [circleIntegral, Set.restrict]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * π)
  have hd : Continuous (fun θ : ℝ => deriv (circleMap z₀ r) θ) := by
    simp only [deriv_circleMap]; exact (continuous_circleMap 0 r).mul continuous_const
  refine Continuous.smul (hd.comp continuous_snd) ?_
  exact hΦ.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk ((continuous_circleMap z₀ r).comp
      continuous_snd))
    fun p => Set.mk_mem_prod p.1.2 (circleMap_mem_sphere z₀ hr p.2)

/-- The `w`-partial of the slice `f(ζ,·)`, defined by the **interior Cauchy derivative formula**
`(2πI)⁻¹ ∮_η f(ζ,η)/(η−w)²`. (Differentiating `f(ζ,·)`'s interior Cauchy representation under the
integral; the only `w`-dependence is the smooth kernel, so this is automatically jointly continuous.) -/
noncomputable def slicePartial (f : ℂ × ℂ → ℂ) (w₀ : ℂ) (rw : ℝ) (ζ w : ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), ((η - w) ^ 2)⁻¹ • f (ζ, η)

/-- **`slicePartial` is the `w`-derivative of the slice.** For `f` continuous on the torus×closed-disc
and holomorphic in `w` on the open disc, `slicePartial f w₀ rw ζ` is `HasDerivAt` of `f(ζ,·)` at each
interior `w`. (Differentiate the interior Cauchy representation under the integral.) -/
theorem slicePartial_hasDerivAt {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw : ℝ} (hrw : 0 < rw)
    (hcont : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw))
    (hdiff : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ ball w₀ rw, DifferentiableAt ℂ (fun w' => f (ζ, w')) η)
    {ζ : ℂ} (hζ : ζ ∈ sphere z₀ rz) {w : ℂ} (hw : w ∈ ball w₀ rw) :
    HasDerivAt (fun w' => f (ζ, w')) (slicePartial f w₀ rw ζ w) w := by
  -- slice continuity on the closed disc
  have gcont : ContinuousOn (fun η => f (ζ, η)) (closedBall w₀ rw) :=
    hcont.comp (Continuous.continuousOn (by fun_prop))
      fun η hη => Set.mk_mem_prod hζ hη
  -- interior Cauchy representation, valid on the open disc
  have grep : ∀ w' ∈ ball w₀ rw,
      f (ζ, w') = (2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), (η - w')⁻¹ • f (ζ, η) := fun w' hw' =>
    (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw' gcont fun x hx => hdiff ζ hζ x hx.1).symm
  -- a small parameter ball around `w` inside the disc
  set dw := dist w w₀ with hdw_def
  have hdw : dw < rw := mem_ball.mp hw
  set δ := (rw - dw) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hsub : closedBall w δ ⊆ ball w₀ rw := fun x hx => by
    rw [mem_ball]; rw [mem_closedBall] at hx
    calc dist x w₀ ≤ dist x w + dw := dist_triangle x w w₀
      _ ≤ δ + dw := by linarith
      _ < rw := by rw [hδ_def]; linarith
  -- `η ≠ w'` for `η` on the contour, `w'` near `w`
  have hpne : ∀ p : ℂ × ℂ, p ∈ closedBall w δ ×ˢ sphere w₀ rw → p.2 - p.1 ≠ 0 := by
    rintro ⟨w', η⟩ ⟨hw', hη⟩
    change η - w' ≠ 0
    have h1 : dist η w₀ = rw := mem_sphere.mp hη
    have h2 : dist w' w₀ < rw := mem_ball.mp (hsub hw')
    rw [sub_ne_zero]
    intro h; rw [h] at h1
    exact absurd h1 (ne_of_lt h2)
  -- joint continuity of the `f`-factor on the parameter ball × contour
  have hfpart : ContinuousOn (fun p : ℂ × ℂ => f (ζ, p.2)) (closedBall w δ ×ˢ sphere w₀ rw) :=
    hcont.comp (Continuous.continuousOn (by fun_prop))
      fun p hp => Set.mk_mem_prod hζ (sphere_subset_closedBall hp.2)
  have hΦ : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ • f (ζ, p.2))
      (closedBall w δ ×ˢ sphere w₀ rw) :=
    (ContinuousOn.inv₀ ((continuous_snd.sub continuous_fst).continuousOn) hpne).smul hfpart
  have hΦ' : ContinuousOn (fun p : ℂ × ℂ => ((p.2 - p.1) ^ 2)⁻¹ • f (ζ, p.2))
      (closedBall w δ ×ˢ sphere w₀ rw) :=
    (ContinuousOn.inv₀ (((continuous_snd.sub continuous_fst).pow 2).continuousOn)
      fun p hp => pow_ne_zero 2 (hpne p hp)).smul hfpart
  have hderiv : ∀ w' ∈ ball w δ, ∀ η ∈ sphere w₀ rw,
      HasDerivAt (fun u => (η - u)⁻¹ • f (ζ, η)) (((η - w') ^ 2)⁻¹ • f (ζ, η)) w' := by
    intro w' hw' η hη
    have hne : η - w' ≠ 0 := hpne (w', η) ⟨ball_subset_closedBall hw', hη⟩
    have h1 : HasDerivAt (fun u : ℂ => η - u) (-1) w' := by
      simpa using (hasDerivAt_id w').const_sub η
    have hk : HasDerivAt (fun u => (η - u)⁻¹) (((η - w') ^ 2)⁻¹) w' := by
      simpa using h1.inv hne
    simpa using hk.smul_const (f (ζ, η))
  have hint := circleIntegral_hasDerivAt (Φ := fun w' η => (η - w')⁻¹ • f (ζ, η))
    (Φ' := fun w' η => ((η - w') ^ 2)⁻¹ • f (ζ, η)) hδ hrw.le hΦ hΦ' hderiv
  have heq : (fun w' => f (ζ, w')) =ᶠ[𝓝 w]
      fun w' => (2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), (η - w')⁻¹ • f (ζ, η) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) fun w' hw' => grep w' hw'
  rw [slicePartial]
  exact (heq.hasDerivAt_iff).mpr (hint.const_smul (2 * π * I : ℂ)⁻¹)

/-- **Joint continuity of `slicePartial`** in `(w, ζ)` on `closedBall w₀ δ ×ˢ sphere z₀ rz`
(`δ < rw`). The `w`-dependence is the smooth Cauchy kernel `(η−w)⁻²`; parametric continuity does the
rest. Form matches `circleIntegral_differentiableOn`'s `Φ'` argument (`p.1 = w`, `p.2 = ζ`). -/
theorem slicePartial_continuousOn {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw δ : ℝ} (hrw : 0 < rw)
    (hδ : δ < rw) (hcont : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw)) :
    ContinuousOn (fun p : ℂ × ℂ => slicePartial f w₀ rw p.2 p.1)
      (closedBall w₀ δ ×ˢ sphere z₀ rz) := by
  have hne : ∀ pr : (ℂ × ℂ) × ℂ,
      pr ∈ (closedBall w₀ δ ×ˢ sphere z₀ rz) ×ˢ sphere w₀ rw → pr.2 - pr.1.1 ≠ 0 := by
    rintro ⟨⟨w, ζ⟩, η⟩ ⟨⟨hw, hζ⟩, hη⟩
    change η - w ≠ 0
    have h1 : dist η w₀ = rw := mem_sphere.mp hη
    have h2 : dist w w₀ ≤ δ := mem_closedBall.mp hw
    rw [sub_ne_zero]; intro h; rw [h] at h1; linarith
  have hfpart : ContinuousOn (fun pr : (ℂ × ℂ) × ℂ => f (pr.1.2, pr.2))
      ((closedBall w₀ δ ×ˢ sphere z₀ rz) ×ˢ sphere w₀ rw) :=
    hcont.comp (Continuous.continuousOn (by fun_prop))
      fun pr hpr => Set.mk_mem_prod hpr.1.2 (sphere_subset_closedBall hpr.2)
  have key : ContinuousOn (fun q : ℂ × ℂ => ∮ η in C(w₀, rw), ((η - q.1) ^ 2)⁻¹ • f (q.2, η))
      (closedBall w₀ δ ×ˢ sphere z₀ rz) := by
    refine circleIntegral_continuousOn_param hrw.le ?_
    exact (ContinuousOn.inv₀ (((continuous_snd.sub (continuous_fst.comp continuous_fst)).pow
      2).continuousOn) fun pr hpr => pow_ne_zero 2 (hne pr hpr)).smul hfpart
  simp only [slicePartial]
  exact key.const_smul _

/-- **The coefficient slice `Aⱼ(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)` is holomorphic in `w`** on the open
`w`-disc — established from *bare* slice-holomorphy + joint continuity (Osgood's hypotheses), using
`slicePartial` as the (continuous) `w`-derivative. This is the keystone that the iterated-Cauchy
route needed; it closes the genuine hard core of the ℂ² bridge. -/
theorem Aj_differentiableOn {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw δ : ℝ} (hrz : 0 < rz) (hrw : 0 < rw)
    (hδ : 0 < δ) (hδrw : δ < rw)
    (hcont : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw))
    (hdiff : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ ball w₀ rw, DifferentiableAt ℂ (fun w' => f (ζ, w')) η)
    (j : ℕ) :
    DifferentiableOn ℂ (fun w => ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      (ball w₀ δ) := by
  have hζne : ∀ p : ℂ × ℂ, p ∈ closedBall w₀ δ ×ˢ sphere z₀ rz → p.2 - z₀ ≠ 0 := by
    rintro ⟨w, ζ⟩ ⟨-, hζ⟩
    change ζ - z₀ ≠ 0
    have hd : dist ζ z₀ = rz := mem_sphere.mp hζ
    rw [sub_ne_zero]; intro h; rw [h, dist_self] at hd; linarith
  have hker : ContinuousOn (fun p : ℂ × ℂ => ((p.2 - z₀) ^ (j + 1))⁻¹)
      (closedBall w₀ δ ×ˢ sphere z₀ rz) :=
    ContinuousOn.inv₀ ((continuous_snd.sub continuous_const).pow _).continuousOn
      fun p hp => pow_ne_zero _ (hζne p hp)
  have hfpart : ContinuousOn (fun p : ℂ × ℂ => f (p.2, p.1)) (closedBall w₀ δ ×ˢ sphere z₀ rz) :=
    hcont.comp (Continuous.continuousOn (by fun_prop))
      fun p hp => Set.mk_mem_prod hp.2 (closedBall_subset_closedBall hδrw.le hp.1)
  refine circleIntegral_differentiableOn (Φ := fun w ζ => ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
    (Φ' := fun w ζ => ((ζ - z₀) ^ (j + 1))⁻¹ • slicePartial f w₀ rw ζ w) hδ hrz.le (hker.smul hfpart)
    ?_ ?_
  · -- `Φ'` continuity: kernel × `slicePartial`
    exact hker.smul (slicePartial_continuousOn hrw hδrw hcont)
  · -- pointwise `w`-derivative
    intro w hw ζ hζ
    simpa using (slicePartial_hasDerivAt hrw hcont hdiff hζ
      (ball_subset_ball hδrw.le hw)).const_smul ((ζ - z₀) ^ (j + 1))⁻¹

/-- The inner `z`-coefficient slice `Aⱼ(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)`. -/
noncomputable def scvA (f : ℂ × ℂ → ℂ) (z₀ : ℂ) (rz : ℝ) (j : ℕ) (w : ℂ) : ℂ :=
  ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w)

/-- `Bⱼ(w) = (2πI)⁻¹·Aⱼ(w)` — the `j`-th `z`-power-series coefficient as a function of `w`. -/
noncomputable def scvB (f : ℂ × ℂ → ℂ) (z₀ : ℂ) (rz : ℝ) (j : ℕ) (w : ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • scvA f z₀ rz j w

/-- `scvCoeff` factors through `scvB`: `c_{jk} = (2πI)⁻¹ ∮_η (η−w₀)^{-(k+1)}·Bⱼ(η)` (definitional). -/
theorem scvCoeff_eq_B (f : ℂ × ℂ → ℂ) (z₀ w₀ : ℂ) (rz rw : ℝ) (j k : ℕ) :
    scvCoeff f z₀ w₀ rz rw j k
      = (2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), ((η - w₀) ^ (k + 1))⁻¹ • scvB f z₀ rz j η := rfl

/-- `scvB` (hence `Aⱼ`) is continuous on the closed `w`-disc. -/
theorem scvB_continuousOn {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw : ℝ} (hrz : 0 < rz) (j : ℕ)
    (hcont : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw)) :
    ContinuousOn (scvB f z₀ rz j) (closedBall w₀ rw) := by
  have hζne : ∀ p : ℂ × ℂ, p ∈ closedBall w₀ rw ×ˢ sphere z₀ rz → p.2 - z₀ ≠ 0 := by
    rintro ⟨w, ζ⟩ ⟨-, hζ⟩
    change ζ - z₀ ≠ 0
    have hd : dist ζ z₀ = rz := mem_sphere.mp hζ
    rw [sub_ne_zero]; intro h; rw [h, dist_self] at hd; linarith
  have hker : ContinuousOn (fun p : ℂ × ℂ => ((p.2 - z₀) ^ (j + 1))⁻¹)
      (closedBall w₀ rw ×ˢ sphere z₀ rz) :=
    ContinuousOn.inv₀ ((continuous_snd.sub continuous_const).pow _).continuousOn
      fun p hp => pow_ne_zero _ (hζne p hp)
  have hfpart : ContinuousOn (fun p : ℂ × ℂ => f (p.2, p.1)) (closedBall w₀ rw ×ˢ sphere z₀ rz) :=
    hcont.comp (Continuous.continuousOn (by fun_prop)) fun p hp => Set.mk_mem_prod hp.2 hp.1
  exact (circleIntegral_continuousOn_param hrz.le (hker.smul hfpart)).const_smul
    (2 * π * I : ℂ)⁻¹

/-- `scvB` (hence `Aⱼ`) is holomorphic on the open `w`-disc. -/
theorem scvB_differentiableOn {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw : ℝ} (hrz : 0 < rz) (hrw : 0 < rw)
    (j : ℕ) (hcont : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw))
    (hdiff : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ ball w₀ rw, DifferentiableAt ℂ (fun w' => f (ζ, w')) η) :
    ∀ η ∈ ball w₀ rw, DifferentiableAt ℂ (scvB f z₀ rz j) η := by
  intro η hη
  have hdη : dist η w₀ < rw := mem_ball.mp hη
  set δ := (dist η w₀ + rw) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; positivity
  have hδrw : δ < rw := by rw [hδ_def]; linarith
  have hηδ : η ∈ ball w₀ δ := by rw [mem_ball, hδ_def]; linarith
  exact ((Aj_differentiableOn hrz hrw hδ hδrw hcont hdiff j).differentiableAt
    (isOpen_ball.mem_nhds hηδ)).const_smul (2 * π * I : ℂ)⁻¹

/-- **The ℕ×ℕ HasSum: `f(z,w) = ∑_{j,k} c_{jk}(z−z₀)^j(w−w₀)^k`.** Iterated Cauchy expansion — `w`-row
sums (`hasSum_w_expansion` on `Bⱼ`, holomorphic+continuous via `scvB_*`), `z`-column sum
(`hasSum_z_expansion'`), glued over `ℕ×ℕ` by `HasSum.sigma_of_hasSum` using `summable_scvCoeff_family`.
Hypothesis: `f` jointly ℂ-differentiable on the closed polydisc (Osgood-style). -/
theorem scvCoeff_hasSum {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw : ℝ} (hrz : 0 < rz) (hrw : 0 < rw)
    (hdiff : ∀ ζ ∈ closedBall z₀ rz, ∀ η ∈ closedBall w₀ rw, DifferentiableAt ℂ f (ζ, η))
    {z w : ℂ} (hz : ‖z - z₀‖ < rz) (hw : ‖w - w₀‖ < rw) :
    HasSum (fun jk : ℕ × ℕ =>
      scvCoeff f z₀ w₀ rz rw jk.1 jk.2 * ((z - z₀) ^ jk.1 * (w - w₀) ^ jk.2)) (f (z, w)) := by
  have hw_cl : w ∈ closedBall w₀ rw := mem_closedBall_iff_norm.mpr hw.le
  have hcont_poly : ContinuousOn f (closedBall z₀ rz ×ˢ closedBall w₀ rw) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩; exact ((hdiff a ha b hb).continuousAt).continuousWithinAt
  have hcont_torus : ContinuousOn f (sphere z₀ rz ×ˢ closedBall w₀ rw) :=
    hcont_poly.mono (Set.prod_mono sphere_subset_closedBall le_rfl)
  -- bound on the torus ⟹ summability of the double family
  obtain ⟨M, hM⟩ := ((isCompact_sphere z₀ rz).prod
    (isCompact_sphere w₀ rw)).exists_bound_of_continuousOn
    (hcont_poly.mono (Set.prod_mono sphere_subset_closedBall sphere_subset_closedBall))
  have hg : Summable (fun jk : ℕ × ℕ =>
      scvCoeff f z₀ w₀ rz rw jk.1 jk.2 * ((z - z₀) ^ jk.1 * (w - w₀) ^ jk.2)) :=
    summable_scvCoeff_family hrz hrw
      (fun ζ hζ η hη => hM (ζ, η) (Set.mk_mem_prod hζ hη)) hz hw
  -- slice differentiabilities
  have hdz : ∀ ζ ∈ ball z₀ rz, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ :=
    fun ζ hζ => (hdiff ζ (ball_subset_closedBall hζ) w hw_cl).comp ζ
      (differentiableAt_id.prodMk (differentiableAt_const w))
  have hcont_z : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ rz) :=
    hcont_poly.comp (Continuous.continuousOn (by fun_prop)) fun ζ hζ => Set.mk_mem_prod hζ hw_cl
  have hdw_slice : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ ball w₀ rw,
      DifferentiableAt ℂ (fun w' => f (ζ, w')) η :=
    fun ζ hζ η hη => (hdiff ζ (sphere_subset_closedBall hζ) η (ball_subset_closedBall hη)).comp η
      ((differentiableAt_const ζ).prodMk differentiableAt_id)
  -- `z`-column sum: `f(z,w) = ∑_j (z−z₀)^j • Bⱼ(w)`
  have hzexp : HasSum (fun j => (z - z₀) ^ j • scvA f z₀ rz j w) ((2 * π * I : ℂ) • f (z, w)) :=
    hasSum_z_expansion' hrz hcont_z hdz hz
  have hrowval : HasSum (fun j => (z - z₀) ^ j • scvB f z₀ rz j w) (f (z, w)) := by
    have h := hzexp.const_smul (2 * π * I : ℂ)⁻¹
    rw [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul] at h
    have hfun : (fun j => (2 * π * I : ℂ)⁻¹ • ((z - z₀) ^ j • scvA f z₀ rz j w))
        = fun j => (z - z₀) ^ j • scvB f z₀ rz j w := by
      funext j; rw [scvB]; exact smul_comm _ _ _
    rwa [hfun] at h
  -- `w`-row sum for each `j`: `∑_k c_{jk}(w−w₀)^k = Bⱼ(w)`
  have hkrow : ∀ j, HasSum (fun k => scvCoeff f z₀ w₀ rz rw j k * (w - w₀) ^ k)
      (scvB f z₀ rz j w) := by
    intro j
    have h2 := (hasSum_w_expansion hrw (scvB_continuousOn hrz j hcont_torus)
      (scvB_differentiableOn hrz hrw j hcont_torus hdw_slice) hw).const_smul (2 * π * I : ℂ)⁻¹
    rw [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul] at h2
    have hfun2 : (fun k => (2 * π * I : ℂ)⁻¹ • ((w - w₀) ^ k •
        ∮ η in C(w₀, rw), ((η - w₀) ^ (k + 1))⁻¹ • scvB f z₀ rz j η))
        = fun k => scvCoeff f z₀ w₀ rz rw j k * (w - w₀) ^ k := by
      funext k; rw [scvCoeff_eq_B]; simp only [smul_eq_mul]; ring
    rwa [hfun2] at h2
  -- assemble over `ℕ × ℕ`
  refine (Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ ℕ)).mp
    (HasSum.sigma_of_hasSum hrowval (fun j => ?_)
      ((Equiv.summable_iff (Equiv.sigmaEquivProd ℕ ℕ)).mpr hg))
  show HasSum (fun k => scvCoeff f z₀ w₀ rz rw j k * ((z - z₀) ^ j * (w - w₀) ^ k))
    ((z - z₀) ^ j • scvB f z₀ rz j w)
  have hk := (hkrow j).const_smul ((z - z₀) ^ j)
  have hfun3 : (fun k => (z - z₀) ^ j • (scvCoeff f z₀ w₀ rz rw j k * (w - w₀) ^ k))
      = fun k => scvCoeff f z₀ w₀ rz rw j k * ((z - z₀) ^ j * (w - w₀) ^ k) := by
    funext k; simp only [smul_eq_mul]; ring
  rwa [hfun3] at hk

/-- **ℂ² bridge / the keystone's analytic core:** a function jointly ℂ-differentiable on a closed
polydisc around `(z₀,w₀)` is `AnalyticAt` there. Packages `scvCoeff_hasSum` (the `ℕ×ℕ` power series)
+ `le_radius_scvSeries` (radius) into a `HasFPowerSeriesOnBall`. This is `osgood`/the SCV bridge in
two variables, sorry-free, from Osgood's hypotheses only. -/
theorem scv_analyticAt {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} {rz rw : ℝ} (hrz : 0 < rz) (hrw : 0 < rw)
    (hdiff : ∀ ζ ∈ closedBall z₀ rz, ∀ η ∈ closedBall w₀ rw, DifferentiableAt ℂ f (ζ, η)) :
    AnalyticAt ℂ f (z₀, w₀) := by
  have hρ0 : 0 < min rz rw := lt_min hrz hrw
  have hρrz : min rz rw ≤ rz := min_le_left rz rw
  have hρrw : min rz rw ≤ rw := min_le_right rz rw
  have hcont_poly : ContinuousOn f (closedBall z₀ rz ×ˢ closedBall w₀ rw) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩; exact ((hdiff a ha b hb).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_sphere z₀ rz).prod
    (isCompact_sphere w₀ rw)).exists_bound_of_continuousOn
    (hcont_poly.mono (Set.prod_mono sphere_subset_closedBall sphere_subset_closedBall))
  have hb_torus : ∀ ζ ∈ sphere z₀ rz, ∀ η ∈ sphere w₀ rw, ‖f (ζ, η)‖ ≤ M :=
    fun ζ hζ η hη => hM (ζ, η) (Set.mk_mem_prod hζ hη)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb_torus (z₀ + rz)
    (by simp [mem_sphere_iff_norm, abs_of_pos hrz]) (w₀ + rw)
    (by simp [mem_sphere_iff_norm, abs_of_pos hrw]))
  have hcbound : ∀ j k, ‖scvCoeff f z₀ w₀ rz rw j k‖ ≤ M / (min rz rw) ^ (j + k) := by
    intro j k
    refine (norm_scvCoeff_le hrz hrw hb_torus j k).trans
      (div_le_div_of_nonneg_left hM0 (pow_pos hρ0 (j + k)) ?_)
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hρ0.le hρrz j) (pow_le_pow_left₀ hρ0.le hρrw k)
      (pow_nonneg hρ0.le k) (pow_nonneg hrz.le j)
  have hs_pos : (0 : ℝ) < min rz rw / 2 := by linarith
  set s : NNReal := (min rz rw / 2).toNNReal with hs_def
  have hsc : (s : ℝ) = min rz rw / 2 := Real.coe_toNNReal _ hs_pos.le
  refine HasFPowerSeriesOnBall.analyticAt
    (p := scvSeries (scvCoeff f z₀ w₀ rz rw)) (r := (s : ENNReal))
    ⟨le_radius_scvSeries hM0 hρ0 hcbound (s := s) (by rw [hsc]; linarith), ?_, ?_⟩
  · rw [ENNReal.coe_pos, ← NNReal.coe_pos, hsc]; exact hs_pos
  · intro y hy
    have hyn : ‖y‖ < min rz rw / 2 := by
      have h := mem_eball_zero_iff.mp hy
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
      have := NNReal.coe_lt_coe.mpr h
      rwa [coe_nnnorm, hsc] at this
    have hyfst : ‖y.1‖ ≤ ‖y‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hysnd : ‖y.2‖ ≤ ‖y‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hkey := scvCoeff_hasSum hrz hrw hdiff (z := z₀ + y.1) (w := w₀ + y.2)
      (by rw [add_sub_cancel_left]; linarith) (by rw [add_sub_cancel_left]; linarith)
    simp only [add_sub_cancel_left] at hkey
    exact hasSum_scvTerm_diag (c := scvCoeff f z₀ w₀ rz rw) y hkey

/-- **The ℂ² holomorphy⇒analyticity bridge (sorry-free).** A function jointly ℂ-differentiable on an
open `U ⊆ ℂ²` is analytic there. This is `bridge_prod`'s base/`osgood` discharged for the two-variable
case, proved directly by the polydisc–Cauchy route (no `osgood` axiom). -/
theorem scv_bridge {f : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  rintro ⟨z₀, w₀⟩ hp
  obtain ⟨u, v, hu_o, hv_o, hz₀u, hw₀v, huv⟩ := isOpen_prod_iff.mp hU z₀ w₀ hp
  obtain ⟨rz, hrz, hballz⟩ := Metric.isOpen_iff.mp hu_o z₀ hz₀u
  obtain ⟨rw, hrw, hballw⟩ := Metric.isOpen_iff.mp hv_o w₀ hw₀v
  refine scv_analyticAt (rz := rz / 2) (rw := rw / 2) (by linarith) (by linarith)
    fun ζ hζ η hη => hf.differentiableAt (hU.mem_nhds (huv (Set.mk_mem_prod
      (hballz (closedBall_subset_ball (by linarith) hζ))
      (hballw (closedBall_subset_ball (by linarith) hη)))))

end
