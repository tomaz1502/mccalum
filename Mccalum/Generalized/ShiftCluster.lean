import Mccalum.Generalized.Lifting
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Translation infrastructure for the multi-cluster assembly

To apply the single-cluster machinery (stated at `t = 0`) at a general real root `t_j`, the section
family is shifted via `taylor t_j (g w) = (g w).comp (X + C t_j)` (root at `t_j` ↦ root at `0`).
Mathlib supplies the shift facts for roots (`rootMultiplicity_eq_rootMultiplicity`) and degree
(`natDegree_taylor`); the new ingredient is that the shifted coefficients stay analytic.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- The coefficients of the Taylor-shifted family stay real-analytic. -/
lemma analyticAt_taylor_coeff {s : ℕ} (N : ℕ) (g : (Fin s → ℝ) → Polynomial ℝ)
    (hdeg : ∀ w, (g w).natDegree ≤ N)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0) (c : ℝ) (j : ℕ) :
    AnalyticAt ℝ (fun w => (taylor c (g w)).coeff j) 0 := by
  have hrepr : (fun w => (taylor c (g w)).coeff j)
      = fun w => ∑ i ∈ Finset.range (N + 1), (g w).coeff i * ((X + C c) ^ i).coeff j := by
    funext w
    conv_lhs => rw [as_sum_range' (g w) (N + 1) (by have := hdeg w; omega : (g w).natDegree < N + 1)]
    rw [map_sum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (monomial i ((g w).coeff i) : Polynomial ℝ) = (g w).coeff i • (X : Polynomial ℝ) ^ i from
        by rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial], map_smul, taylor_X_pow,
      Polynomial.coeff_smul, smul_eq_mul]
  rw [hrepr]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (hcoeff i).mul analyticAt_const

end
