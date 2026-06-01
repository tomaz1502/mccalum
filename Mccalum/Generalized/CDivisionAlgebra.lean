import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum

/-!
# Brick: the polynomial difference-quotient (division-by-`W` remainder structure)

For a polynomial `W`, `W(ζ) − W(t) = (ζ − t)·Q(ζ, t)` with an explicit `Q` that is, in the `t`
variable, a polynomial of degree `< deg W` whose coefficients are polynomials in `ζ`. This is the
algebraic heart of the "division by a Weierstrass polynomial" step of the Cauchy-integral proof of
`weierstrass_division`: it makes the remainder
`r(z,t) = (2πi)⁻¹ ∮ (F/G)·(W(ζ)−W(t))/(ζ−t) dζ` a degree-`<m` polynomial in `t` (integrate the finite
`Q`-sum term by term). Pure algebra — no analysis.
-/

noncomputable section

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **Difference-quotient factorization.** `W(ζ) − W(t) = (ζ − t)·∑_j W_j·∑_{i<j} ζ^i t^{j-1-i}`.
The inner double sum is `Q(ζ,t)`; in the `t`-variable every monomial `t^{j-1-i}` has degree
`≤ deg W − 1`. -/
theorem eval_sub_eval_eq_mul (W : Polynomial R) (ζ t : R) :
    W.eval ζ - W.eval t
      = (ζ - t) * ∑ j ∈ range (W.natDegree + 1),
          W.coeff j * ∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc W.coeff j * ζ ^ j - W.coeff j * t ^ j
      = W.coeff j * (ζ ^ j - t ^ j) := by ring
    _ = W.coeff j * ((∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i)) * (ζ - t)) := by
          rw [geom_sum₂_mul]
    _ = (ζ - t) * (W.coeff j * ∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i)) := by ring

/-- Each `t`-monomial of `Q(ζ, t)` has degree `< natDegree W` in `t` (the inner exponent
`j - 1 - i ≤ natDegree − 1` for `i < j ≤ natDegree`). This is the degree-`<m` property of the
division remainder, read off the double sum directly. -/
theorem diffQuotient_tdeg_lt (W : Polynomial R) (ζ : R) {j i : ℕ}
    (hj : j ∈ range (W.natDegree + 1)) (hi : i ∈ range j) (hpos : 0 < W.natDegree) :
    j - 1 - i < W.natDegree := by
  simp only [Finset.mem_range] at hj hi; omega
