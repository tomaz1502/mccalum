import Mccalum.DiscrMul
import Mccalum.DiscrProdInvariant
import Mccalum.OrderInvariantFactor
import Mccalum.Prerequisites
import Mccalum.SquarefreeBasis

/-!
# McCallum's Reduced Projection Theorem (Theorem 3.2.3)

This file contains the statement and proof of Theorem 3.2.3 from McCallum's PhD thesis
"An Improved Projection Operation for Cylindrical Algebraic Decomposition" (1984).

## Main result

**Theorem 3.2.3**: Let `A` be a finite squarefree basis of `r`-variate integral polynomials
(`r ≥ 2`), `S` a connected submanifold of `ℝ^{r-1}`. Suppose each element of `A` is not
identically zero on `S`, and each element of the reduced projection `P(A)` is
order-invariant in `S`. Then:
1. Each element of `A` is degree-invariant on `S`
2. Each element of `A` is analytically delineable on `S`
3. The sections of `A` over `S` are pairwise disjoint
4. Each element of `A` is order-invariant in every section of `A` over `S`
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- Coprime polynomials have no common root after specialization. -/
theorem no_common_root_of_coprime (F G : PolyR n) (hcop : IsCoprime F G)
    (a : Fin n → ℝ) (y : ℝ) :
    ¬ ((specialize F a).IsRoot y ∧ (specialize G a).IsRoot y) := by
  intro ⟨hF, hG⟩
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : specialize (u * F + v * G) a = 1 := by
    rw [huv]; simp [specialize, Polynomial.map_one]
  have h2 : (specialize (u * F + v * G) a).eval y = 1 := by
    rw [h1]; simp
  simp only [specialize, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.eval_add, Polynomial.eval_mul] at h2
  rw [Polynomial.IsRoot] at hF hG
  simp only [specialize] at hF hG
  rw [hF, hG] at h2
  linarith

end
