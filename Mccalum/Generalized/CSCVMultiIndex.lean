import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The `ℂⁿ` multi-index term — foundation of the `n`-variable SCV bridge

The polarization-free route to the `ℂⁿ` holomorphy⇒analyticity bridge generalizes the proven `ℂ²`
`scvTerm`/`scvCoeff` construction to `ℕⁿ` multi-indices with **scalar** coefficients (so the
coefficient bounds are clean iterated 1-variable Cauchy estimates — no operator-norm polarization).

This file builds the foundational block: `mtTerm c assign`, the asymmetric `N`-multilinear map on
`Fin n → ℂ` (= `ℂⁿ`) whose `i`-th slot reads coordinate `assign i`. Its diagonal at `y` is
`c · ∏ᵢ y (assign i)` (so for an `assign` realizing a multi-index `α`, the diagonal is `c · ∏ⱼ yⱼ^αⱼ`),
and its operator norm is `≤ ‖c‖`. This generalizes `CSCVCombination.mlTerm`/`CSCVBridge.scvTerm` from
2 coordinates (`fst`/`snd`) to `n` coordinates (Pi-projections).
-/

noncomputable section

open ContinuousMultilinearMap

/-- The `j`-th coordinate projection `ℂⁿ → ℂ` has operator norm `≤ 1`. -/
theorem norm_proj_pi_le {n : ℕ} (i : Fin n) :
    ‖(ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

/-- The asymmetric multi-index term: the `N`-multilinear map on `ℂⁿ` whose `i`-th argument is read in
coordinate `assign i`. Diagonal `c · ∏ᵢ y(assign i)`, norm `≤ ‖c‖`. -/
def mtTerm {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => Fin n → ℂ) ℂ :=
  c • (ContinuousMultilinearMap.mkPiAlgebraFin ℂ N ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (assign i))

/-- **Diagonal of `mtTerm`:** `mtTerm c assign (fun _ => y) = c · ∏ᵢ y (assign i)`. -/
theorem mtTerm_apply_diag {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) (y : Fin n → ℂ) :
    mtTerm c assign (fun _ => y) = c * ∏ i : Fin N, y (assign i) := by
  rw [mtTerm, ContinuousMultilinearMap.smul_apply, compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  simp [smul_eq_mul]

/-- **Operator-norm bound:** `‖mtTerm c assign‖ ≤ ‖c‖`. -/
theorem norm_mtTerm_le {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) : ‖mtTerm c assign‖ ≤ ‖c‖ := by
  rw [mtTerm, norm_smul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine (norm_compContinuousLinearMap_le _ _).trans ?_
  have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ N ℂ‖ ≤ 1 :=
    norm_mkPiAlgebraFin_le.trans (by rw [norm_one, max_self])
  exact mul_le_one₀ hmk (Finset.prod_nonneg fun i _ => norm_nonneg _)
    (Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_proj_pi_le _)

/-- **The multi-index power series** on `ℂⁿ`: its degree-`N` term sums `mtTerm` over all coordinate
assignments `assign : Fin N → Fin n` (each `assign` is a monomial of total degree `N`). The scalar
coefficient `c N assign` will be the `n`-fold nested Cauchy integral. -/
def mtSeries {n : ℕ} (c : (N : ℕ) → (Fin N → Fin n) → ℂ) :
    FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ :=
  fun N => ∑ assign : Fin N → Fin n, mtTerm (c N assign) assign

/-- **Diagonal of `mtSeries`:** `(mtSeries c) N (y,…,y) = ∑_{assign} c N assign · ∏ᵢ y(assign i)`. -/
theorem mtSeries_apply_diag {n : ℕ} (c : (N : ℕ) → (Fin N → Fin n) → ℂ) (N : ℕ) (y : Fin n → ℂ) :
    mtSeries c N (fun _ => y) = ∑ assign : Fin N → Fin n, c N assign * ∏ i : Fin N, y (assign i) := by
  rw [mtSeries, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl fun assign _ => mtTerm_apply_diag _ _ _

/-- **Norm bound on `mtSeries`:** `‖(mtSeries c) N‖ ≤ ∑_{assign} ‖c N assign‖`. -/
theorem norm_mtSeries_le {n : ℕ} (c : (N : ℕ) → (Fin N → Fin n) → ℂ) (N : ℕ) :
    ‖mtSeries c N‖ ≤ ∑ assign : Fin N → Fin n, ‖c N assign‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun assign _ => norm_mtTerm_le _ _)

/-- **Radius bound for `mtSeries`** from the `n`-fold Cauchy coefficient bound `‖c N assign‖ ≤ M/rᴺ`:
any `s` with `s·n < r` is below the radius. (The `nᴺ` count of degree-`N` monomials shrinks the
effective radius by `n` — harmless for `AnalyticAt`; crucially, **no polarization** is involved
because the coefficients are scalars.) -/
theorem le_radius_mtSeries {n : ℕ} {c : (N : ℕ) → (Fin N → Fin n) → ℂ} {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hb : ∀ N assign, ‖c N assign‖ ≤ M / r ^ N) {s : NNReal}
    (hs : (s : ℝ) * n < r) :
    (s : ENNReal) ≤ (mtSeries c).radius := by
  set a : ℝ := (s : ℝ) * n / r with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := (div_lt_one hr).mpr hs
  have hmaj : Summable (fun N : ℕ => M * a ^ N) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  apply (mtSeries c).le_radius_of_summable
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hmaj
  calc ‖mtSeries c N‖ * (s : ℝ) ^ N
      ≤ (∑ _assign : Fin N → Fin n, M / r ^ N) * (s : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right
          ((norm_mtSeries_le c N).trans (Finset.sum_le_sum fun assign _ => hb N assign))
          (by positivity)
    _ = M * a ^ N := by
        have hcard : (Fintype.card (Fin N → Fin n) : ℝ) = (n : ℝ) ^ N := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ha_def, div_pow, mul_pow]
        field_simp

/-- **Summability of the multi-index coefficient family** over all assignments `⟨N, assign⟩`, from the
`n`-fold Cauchy bound and `n·‖y‖ < r`. (Dominated by `M·(n‖y‖/r)ᴺ`; the per-degree fiber is finite.) -/
theorem summable_mt_family {n : ℕ} {c : (N : ℕ) → (Fin N → Fin n) → ℂ} {M r : ℝ}
    (hr : 0 < r) (hb : ∀ N assign, ‖c N assign‖ ≤ M / r ^ N) {y : Fin n → ℂ}
    (hy : (n : ℝ) * ‖y‖ < r) :
    Summable (fun p : Σ N : ℕ, Fin N → Fin n => c p.1 p.2 * ∏ i : Fin p.1, y (p.2 i)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) ((hb 0 (fun i => i.elim0)).trans_eq (by simp))
  set a : ℝ := (n : ℝ) * ‖y‖ / r with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := (div_lt_one hr).mpr hy
  -- the per-degree majorant `M·(n‖y‖/r)ᴺ` is summable
  have hmaj : Summable (fun N : ℕ => M * a ^ N) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  refine Summable.of_norm ((summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
    ⟨fun N => (hasSum_fintype _).summable, ?_⟩)
  · refine hmaj.of_nonneg_of_le (fun N => by positivity) fun N => ?_
    rw [tsum_fintype]
    calc ∑ assign : Fin N → Fin n, ‖c N assign * ∏ i : Fin N, y (assign i)‖
        ≤ ∑ _assign : Fin N → Fin n, M / r ^ N * ‖y‖ ^ N := by
          refine Finset.sum_le_sum fun assign _ => ?_
          rw [norm_mul, norm_prod]
          refine mul_le_mul (hb N assign) ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
            (by positivity)
          calc ∏ i : Fin N, ‖y (assign i)‖ ≤ ∏ _i : Fin N, ‖y‖ :=
                Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => norm_le_pi_norm y _
            _ = ‖y‖ ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = M * a ^ N := by
          have hcard : (Fintype.card (Fin N → Fin n) : ℝ) = (n : ℝ) ^ N := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ha_def, div_pow, mul_pow]
          field_simp

/-- **The diagonal `HasSum` regrouped by degree.** Given the `n`-fold Cauchy bound and `n·‖y‖ < r`,
the degree-`N` diagonal values of `mtSeries` sum to the total over all assignments — `∑_N (mtSeries c)
N (y,…,y) = ∑'_{⟨N,assign⟩} c N assign · ∏ᵢ y(assign i)`. (The "value `= f`" half — the `n`-fold
iterated Cauchy — is the remaining step; this provides the convergence/regrouping half.) -/
theorem mtSeries_diag_hasSum {n : ℕ} {c : (N : ℕ) → (Fin N → Fin n) → ℂ} {M r : ℝ}
    (hr : 0 < r) (hb : ∀ N assign, ‖c N assign‖ ≤ M / r ^ N) {y : Fin n → ℂ}
    (hy : (n : ℝ) * ‖y‖ < r) :
    HasSum (fun N => mtSeries c N (fun _ => y))
      (∑' p : Σ N : ℕ, Fin N → Fin n, c p.1 p.2 * ∏ i : Fin p.1, y (p.2 i)) := by
  have hsum := summable_mt_family hr hb hy
  have hsig := hsum.hasSum.sigma fun N =>
    hasSum_fintype fun assign : Fin N → Fin n => c N assign * ∏ i : Fin N, y (assign i)
  rw [funext fun N => mtSeries_apply_diag c N y]
  exact hsig

end
