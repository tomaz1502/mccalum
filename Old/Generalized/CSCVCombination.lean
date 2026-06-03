import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The multilinear term for the SCV combination lemma

The inductive step of the `ℂⁿ` holomorphy⇒analyticity bridge (`bridge_step`, the multivariable
Weierstrass combination) needs the joint power series of
`f(z,w) = ∑ⱼ (z−z₀)ʲ·Bⱼ(w)` on `ℂ × E'`, where each `Bⱼ : E' → ℂ` is analytic with power series `qⱼ`.
The degree-`n` term of the joint series is `∑_{j+k=n} (z-monomial)ʲ ⊗ qⱼ,ₖ`. This file builds the
single block `mlTerm b k` — the asymmetric multilinear map on `(ℂ × E')` whose diagonal is
`sᵏ • b(t,…,t)` with operator norm `≤ ‖b‖` — generalizing `scvTerm` (scalar coefficients) to
`ContinuousMultilinearMap`-valued coefficients `b = qⱼ,ₖ`.
-/

noncomputable section

open ContinuousMultilinearMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- The `Finset` of the first `k` indices of `Fin (k + m)`. -/
def firstFin (k m : ℕ) : Finset (Fin (k + m)) := Finset.univ.map (Fin.castAddEmb m)

theorem firstFin_card (k m : ℕ) : (firstFin k m).card = k := by
  rw [firstFin, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem firstFin_compl_card (k m : ℕ) : (firstFin k m)ᶜ.card = m := by
  rw [Finset.card_compl, firstFin_card, Fintype.card_fin]; omega

/-- **The multilinear block** `mlTerm b k` on `Fin (k + m) → ℂ × E'`: takes the product of the first
`k` coordinates' `ℂ`-parts times `b` applied to the last `m` coordinates' `E'`-parts. Its diagonal is
`sᵏ • b(t,…,t)` and `‖mlTerm b k‖ ≤ ‖b‖`. -/
def mlTerm {m : ℕ} (b : ContinuousMultilinearMap ℂ (fun _ : Fin m => E') ℂ) (k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (k + m) => ℂ × E') ℂ :=
  (curryFinFinset ℂ (ℂ × E') ℂ (firstFin_card k m) (firstFin_compl_card k m)).symm
    (((ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst ℂ ℂ E')).smulRight
      (b.compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℂ ℂ E')))

/-- **Diagonal of `mlTerm`:** `mlTerm b k (fun _ => (s, t)) = sᵏ • b(t,…,t)`. -/
theorem mlTerm_apply_diag {m : ℕ} (b : ContinuousMultilinearMap ℂ (fun _ : Fin m => E') ℂ) (k : ℕ)
    (s : ℂ) (t : E') : mlTerm b k (fun _ => (s, t)) = s ^ k • b (fun _ => t) := by
  rw [mlTerm, curryFinFinset_symm_apply_const]
  simp only [ContinuousMultilinearMap.smulRight_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  congr 1
  rw [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  simp

/-- **Operator-norm bound:** `‖mlTerm b k‖ ≤ ‖b‖`. -/
theorem norm_mlTerm_le {m : ℕ} (b : ContinuousMultilinearMap ℂ (fun _ : Fin m => E') ℂ) (k : ℕ) :
    ‖mlTerm b k‖ ≤ ‖b‖ := by
  rw [mlTerm, LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_smulRight]
  have hsc : ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
      (fun _ : Fin k => ContinuousLinearMap.fst ℂ ℂ E')‖ ≤ 1 := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ ≤ 1 :=
      ContinuousMultilinearMap.norm_mkPiAlgebraFin_le.trans (by rw [norm_one, max_self])
    refine mul_le_one₀ hmk (Finset.prod_nonneg fun i _ => norm_nonneg _)
      (Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ContinuousLinearMap.norm_fst_le ..)
  have hB : ‖b.compContinuousLinearMap (fun _ : Fin m => ContinuousLinearMap.snd ℂ ℂ E')‖ ≤ ‖b‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc ‖b‖ * ∏ _i : Fin m, ‖ContinuousLinearMap.snd ℂ ℂ E'‖
        ≤ ‖b‖ * 1 := by
          gcongr
          exact Finset.prod_le_one (fun i _ => norm_nonneg _)
            (fun i _ => ContinuousLinearMap.norm_snd_le ..)
      _ = ‖b‖ := mul_one _
  calc ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst ℂ ℂ E')‖ *
      ‖b.compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℂ ℂ E')‖
      ≤ 1 * ‖b‖ := by gcongr
    _ = ‖b‖ := one_mul _

/-- The `degree-n` term, with the block `mlTerm (q k (n-k)) k` transported `Fin (k+(n-k)) → Fin n`. -/
def mlCoeffTerm (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) (n k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × E') ℂ :=
  if h : k ≤ n then (mlTerm (q k (n - k)) k).domDomCongr (finCongr (Nat.add_sub_cancel' h)) else 0

/-- **The joint power series** `f(z,w) = ∑ⱼ (z−z₀)ʲBⱼ(w)`: its degree-`n` term is `∑_{k≤n} mlTerm qₖ,ₙ₋ₖ`. -/
def mlSeries (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) : FormalMultilinearSeries ℂ (ℂ × E') ℂ :=
  fun n => ∑ k ∈ Finset.range (n + 1), mlCoeffTerm q n k

theorem mlCoeffTerm_apply_diag (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) {n k : ℕ} (hk : k ≤ n)
    (s : ℂ) (t : E') :
    mlCoeffTerm q n k (fun _ => (s, t)) = s ^ k • q k (n - k) (fun _ => t) := by
  rw [mlCoeffTerm, dif_pos hk, ContinuousMultilinearMap.domDomCongr_apply, mlTerm_apply_diag]

theorem norm_mlCoeffTerm_le (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) (n k : ℕ) :
    ‖mlCoeffTerm q n k‖ ≤ ‖q k (n - k)‖ := by
  rw [mlCoeffTerm]
  split_ifs with h
  · rw [ContinuousMultilinearMap.norm_domDomCongr]; exact norm_mlTerm_le _ _
  · rw [norm_zero]; exact norm_nonneg _

/-- **Diagonal of `mlSeries`:** `(mlSeries q) n (s,t)ⁿ = ∑_{k≤n} sᵏ • qₖ,ₙ₋ₖ(t,…,t)`. -/
theorem mlSeries_apply_diag (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) (n : ℕ) (s : ℂ) (t : E') :
    mlSeries q n (fun _ => (s, t))
      = ∑ k ∈ Finset.range (n + 1), s ^ k • q k (n - k) (fun _ => t) := by
  rw [mlSeries, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k hk =>
    mlCoeffTerm_apply_diag q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) s t

/-- **Norm bound on `mlSeries`:** `‖(mlSeries q) n‖ ≤ ∑_{k≤n} ‖qₖ,ₙ₋ₖ‖`. -/
theorem norm_mlSeries_le (q : ℕ → FormalMultilinearSeries ℂ E' ℂ) (n : ℕ) :
    ‖mlSeries q n‖ ≤ ∑ k ∈ Finset.range (n + 1), ‖q k (n - k)‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mlCoeffTerm_le q n k)

/-- **Radius bound for `mlSeries`** from the Cauchy coefficient bound `‖qₖ,ₘ‖ ≤ M/(rzᵏ·rwᵐ)`: any
`s < rz, rw` is below the radius of convergence. (The double `(n+1)` degeneracy — `(n+1)` terms in the
degree-`n` sum, each `≤ cⁿ` — is absorbed by summability of `(n+1)cⁿ`, `c = s/min(rz,rw) < 1`.) -/
theorem le_radius_mlSeries {q : ℕ → FormalMultilinearSeries ℂ E' ℂ} {M rz rw : ℝ}
    (hM : 0 ≤ M) (hrz : 0 < rz) (hrw : 0 < rw)
    (hb : ∀ k m, ‖q k m‖ ≤ M / (rz ^ k * rw ^ m)) {s : NNReal}
    (hs1 : (s : ℝ) < rz) (hs2 : (s : ℝ) < rw) :
    (s : ENNReal) ≤ (mlSeries q).radius := by
  set a : ℝ := (s : ℝ) / rz with ha_def
  set b : ℝ := (s : ℝ) / rw with hb_def
  have ha0 : 0 ≤ a := div_nonneg s.2 hrz.le
  have hb0 : 0 ≤ b := div_nonneg s.2 hrw.le
  set c : ℝ := max a b with hc_def
  have hc0 : 0 ≤ c := le_max_of_le_left ha0
  have hc1 : c < 1 := max_lt ((div_lt_one hrz).mpr hs1) ((div_lt_one hrw).mpr hs2)
  -- majorant `(n+1)·M·cⁿ` is summable
  have hmaj : Summable (fun n : ℕ => ((n : ℝ) + 1) * M * c ^ n) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) * c ^ n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := c)
        (by rwa [Real.norm_eq_abs, abs_of_nonneg hc0])
    have h2 : Summable (fun n : ℕ => c ^ n) := summable_geometric_of_lt_one hc0 hc1
    refine ((h1.add h2).mul_left M).congr fun n => ?_
    ring
  apply (mlSeries q).le_radius_of_summable
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  -- `‖mlSeries q n‖ · sⁿ ≤ (n+1)·M·cⁿ`
  have hcoeff : ‖mlSeries q n‖ ≤ ∑ k ∈ Finset.range (n + 1), M / (rz ^ k * rw ^ (n - k)) :=
    (norm_mlSeries_le q n).trans (Finset.sum_le_sum fun k _ => hb k (n - k))
  calc ‖mlSeries q n‖ * (s : ℝ) ^ n
      ≤ (∑ k ∈ Finset.range (n + 1), M / (rz ^ k * rw ^ (n - k))) * (s : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = ∑ k ∈ Finset.range (n + 1), M * (a ^ k * b ^ (n - k)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ha_def, hb_def, div_pow, div_pow]
        rw [show (s : ℝ) ^ n = (s : ℝ) ^ k * (s : ℝ) ^ (n - k) by
          rw [← pow_add, Nat.add_sub_cancel' hkn]]
        field_simp
    _ ≤ ∑ _k ∈ Finset.range (n + 1), M * c ^ n := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine mul_le_mul_of_nonneg_left ?_ hM
        calc a ^ k * b ^ (n - k) ≤ c ^ k * c ^ (n - k) :=
              mul_le_mul (pow_le_pow_left₀ ha0 (le_max_left a b) k)
                (pow_le_pow_left₀ hb0 (le_max_right a b) (n - k)) (pow_nonneg hb0 _)
                (pow_nonneg hc0 k)
          _ = c ^ n := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    _ = ((n : ℝ) + 1) * M * c ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **Generic diagonal regroup:** an `ℕ × ℕ` `HasSum` regroups into the degree-`n` antidiagonal sums. -/
theorem hasSum_antidiagonal {g : ℕ × ℕ → ℂ} {S : ℂ} (h : HasSum g S) :
    HasSum (fun n => ∑ k ∈ Finset.range (n + 1), g (k, n - k)) S := by
  have hσ : HasSum (g ∘ Finset.sigmaAntidiagonalEquivProd) S :=
    Finset.sigmaAntidiagonalEquivProd.hasSum_iff.mpr h
  have hsig := hσ.sigma fun n => hasSum_fintype fun x : ↥(Finset.antidiagonal n) =>
    (g ∘ Finset.sigmaAntidiagonalEquivProd) ⟨n, x⟩
  have hfeq : (fun n => ∑ x : ↥(Finset.antidiagonal n),
        (g ∘ Finset.sigmaAntidiagonalEquivProd) ⟨n, x⟩)
      = fun n => ∑ k ∈ Finset.range (n + 1), g (k, n - k) := by
    funext n
    simp only [Function.comp_apply, Finset.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal n) g,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hfeq] at hsig
  exact hsig

/-- **The combination lemma (analytic core of `bridge_step`).** Given the coefficient functions `Bₖ`
with power series `qₖ` (uniform Cauchy bound `‖qₖ,ₘ‖ ≤ M/(rzᵏ·rwᵐ)`, `w`-expansion `hA`) and the
`z`-series `hC` (`f(z,w) = ∑ₖ (z−z₀)ᵏ Bₖ(w)`), the function `f` is analytic at `(z₀, w₀)`. -/
theorem combination_analyticAt {f : ℂ × E' → ℂ} {z₀ : ℂ} {w₀ : E'}
    {q : ℕ → FormalMultilinearSeries ℂ E' ℂ} {B : ℕ → E' → ℂ} {M rz rw : ℝ}
    (hM : 0 ≤ M) (hrz : 0 < rz) (hrw : 0 < rw)
    (hb : ∀ k m, ‖q k m‖ ≤ M / (rz ^ k * rw ^ m))
    (hA : ∀ (k : ℕ) (t : E'), ‖t‖ < rw → HasSum (fun m => q k m (fun _ => t)) (B k (w₀ + t)))
    (hC : ∀ (s : ℂ) (t : E'), ‖s‖ < rz → ‖t‖ < rw →
      HasSum (fun k => s ^ k • B k (w₀ + t)) (f (z₀ + s, w₀ + t))) :
    AnalyticAt ℂ f (z₀, w₀) := by
  have hρ0 : 0 < min rz rw := lt_min hrz hrw
  have hs_pos : (0 : ℝ) < min rz rw / 2 := by linarith
  set s₀ : NNReal := (min rz rw / 2).toNNReal with hs0_def
  have hsc : (s₀ : ℝ) = min rz rw / 2 := Real.coe_toNNReal _ hs_pos.le
  have hs0rz : (s₀ : ℝ) < rz := by rw [hsc]; have := min_le_left rz rw; linarith
  have hs0rw : (s₀ : ℝ) < rw := by rw [hsc]; have := min_le_right rz rw; linarith
  -- norm of a power-series term on a constant tuple
  have hqle : ∀ (k m : ℕ) (t : E'), ‖q k m (fun _ => t)‖ ≤ ‖q k m‖ * ‖t‖ ^ m := fun k m t => by
    refine ((q k m).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine HasFPowerSeriesOnBall.analyticAt (p := mlSeries q) (r := (s₀ : ENNReal))
    ⟨le_radius_mlSeries hM hrz hrw hb hs0rz hs0rw, ?_, ?_⟩
  · rw [ENNReal.coe_pos, ← NNReal.coe_pos, hsc]; exact hs_pos
  · intro y hy
    obtain ⟨s, t⟩ := y
    have hst : ‖(s, t)‖ < min rz rw / 2 := by
      have h := mem_eball_zero_iff.mp hy
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
      have := NNReal.coe_lt_coe.mpr h
      rwa [coe_nnnorm, hsc] at this
    have hsfst : ‖s‖ ≤ ‖(s, t)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have htsnd : ‖t‖ ≤ ‖(s, t)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hs_lt : ‖s‖ < rz := by
      have := min_le_left rz rw; linarith [hsfst, hst]
    have ht_lt : ‖t‖ < rw := by
      have := min_le_right rz rw; linarith [htsnd, hst]
    -- the `ℕ × ℕ` family is summable (dominated by a product of two geometrics)
    have hsummable : Summable (fun km : ℕ × ℕ => s ^ km.1 • q km.1 km.2 (fun _ => t)) := by
      have ha1 : ‖s‖ / rz < 1 := (div_lt_one hrz).mpr hs_lt
      have hb1 : ‖t‖ / rw < 1 := (div_lt_one hrw).mpr ht_lt
      have hmaj : Summable (fun km : ℕ × ℕ => M * ((‖s‖ / rz) ^ km.1 * (‖t‖ / rw) ^ km.2)) :=
        ((Summable.mul_of_nonneg (summable_geometric_of_lt_one (by positivity) ha1)
          (summable_geometric_of_lt_one (by positivity) hb1)
          (fun n => by positivity) fun n => by positivity)).mul_left M
      refine Summable.of_norm
        (Summable.of_nonneg_of_le (fun km => norm_nonneg _) (fun km => ?_) hmaj)
      rw [norm_smul, norm_pow]
      calc ‖s‖ ^ km.1 * ‖q km.1 km.2 (fun _ => t)‖
          ≤ ‖s‖ ^ km.1 * (M / (rz ^ km.1 * rw ^ km.2) * ‖t‖ ^ km.2) := by
            gcongr
            exact (hqle km.1 km.2 t).trans (by gcongr; exact hb km.1 km.2)
        _ = M * ((‖s‖ / rz) ^ km.1 * (‖t‖ / rw) ^ km.2) := by
            rw [div_pow, div_pow]; field_simp
    -- value: the `ℕ × ℕ` iterated sum equals `f`, then regroup by total degree
    have hnn : HasSum (fun km : ℕ × ℕ => s ^ km.1 • q km.1 km.2 (fun _ => t))
        (f (z₀ + s, w₀ + t)) := by
      refine (Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ ℕ)).mp
        (HasSum.sigma_of_hasSum (hC s t hs_lt ht_lt) (fun k => ?_)
          ((Equiv.summable_iff (Equiv.sigmaEquivProd ℕ ℕ)).mpr hsummable))
      show HasSum (fun m => s ^ k • q k m (fun _ => t)) (s ^ k • B k (w₀ + t))
      exact (hA k t ht_lt).const_smul (s ^ k)
    show HasSum (fun n => mlSeries q n (fun _ => (s, t))) (f (z₀ + s, w₀ + t))
    have hreg := hasSum_antidiagonal hnn
    have hFG : (fun n => ∑ k ∈ Finset.range (n + 1),
          (fun km : ℕ × ℕ => s ^ km.1 • q km.1 km.2 (fun _ => t)) (k, n - k))
        = fun n => mlSeries q n (fun _ : Fin n => (s, t)) := by
      funext n
      rw [mlSeries_apply_diag]
    rw [hFG] at hreg
    exact hreg

end

