import Mccalum.Prerequisites
import Mccalum.DiscrProdInvariant
import Mccalum.SquarefreeBasis
import Mccalum.Generalized.SimpleRoots
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Generalized Lifting Theorem (Theorem 3.2.1')

Proof of the generalized lifting theorem, which replaces the discriminant hypothesis
of the original Theorem 3.2.1 with an arbitrary nonzero element
`P ∈ ⟨f, ∂f/∂xᵣ⟩ ∩ ℝ[x]` that is order-invariant on `S`.

## Proof outline

The proof splits into two cases by the dimension `s` of `S`:

- **Case s = r - 1** (S is open): `P` nonzero and order-invariant on an open connected set
  forces `P` to be nowhere-vanishing. Since `P ∈ ⟨f, f'⟩`, this means `f` has no repeated
  roots at any point of `S`. The implicit function theorem gives simple root sections.

- **Case 1 ≤ s ≤ r - 2** (S has positive codimension): After a coordinate change (submanifold
  chart), complexification, and Weierstrass preparation `g = u·h`, we use the elimination
  ideal structure: `P̃ ∈ ⟨h, h'⟩ ∩ O(Δ) = (disc(h))`, so `P̃ = disc(h)·Q`. The order
  additivity lemma then forces `disc(h)` to be order-invariant. Zariski's theorem applies.

## References

- `thesis/generalized/proof.tex`: Full informal proof.
- McCallum, "An Improved Projection Operation for CAD" (1985), §3.3.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-! ### Case s = r - 1: S is open -/

/-- A nonzero multivariate polynomial over `ℝ` cannot vanish on all of a nonempty
open set. This follows from `MvPolynomial.funext_set` applied to an open box
(product of open intervals) contained in the open set. -/
theorem mvpoly_nonzero_on_open (P : MvPolyR n) (hP : P ≠ 0)
    (S : Set (Fin n → ℝ)) (hS_open : IsOpen S) (hS_ne : S.Nonempty) :
    ∃ a ∈ S, MvPolynomial.eval a P ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hP
  obtain ⟨a₀, ha₀⟩ := hS_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS_open a₀ ha₀
  set s := fun i : Fin n => Set.Ioo (a₀ i - ε) (a₀ i + ε) with hs_def
  have hs_inf : ∀ i, (s i).Infinite := by
    intro i; exact Set.Ioo_infinite (by linarith)
  have hpi_sub : Set.pi Set.univ s ⊆ S := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have := hx i (Set.mem_univ i)
    rw [hs_def, Set.mem_Ioo] at this
    rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hsub : ∀ x ∈ Set.pi Set.univ s, MvPolynomial.eval x P = MvPolynomial.eval x 0 := by
    intro x hx
    simp [hall x (hpi_sub hx)]
  exact MvPolynomial.funext_set s hs_inf hsub

/-- When `S` is open and connected, an order-invariant nonzero polynomial on `S` is
nowhere-vanishing. This is because on an open connected subset of `ℝⁿ`, a polynomial
with constant vanishing order is either identically zero or has order 0 everywhere. -/
theorem order_invariant_nowhere_vanishing_on_open
    (S : Set (Fin n → ℝ))
    (P : MvPolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hP_ne : P ≠ 0)
    (hP_oi : OrderInvariantMv P S) :
    ∀ a ∈ S, MvPolynomial.eval a P ≠ 0 := by
  obtain ⟨a₀, ha₀S, ha₀_ne⟩ := mvpoly_nonzero_on_open P hP_ne S hS_open hS_conn.1
  have hord₀ : polyOrder n P a₀ = 0 := (polyOrder_zero_iff n P a₀).mpr ha₀_ne
  intro a ha
  have hord : polyOrder n P a = 0 := by rw [hP_oi a ha a₀ ha₀S]; exact hord₀
  exact (polyOrder_zero_iff n P a).mp hord

/-- If `P ∈ ⟨f, f'⟩ ∩ ℝ[x]` and `P(a) ≠ 0`, then `f(a, ·)` has no repeated roots.

The proof evaluates the Bézout identity `C(P) = A·f + B·f'` at `(a, y)`: if `y` is a
common root of `f(a,·)` and `f'(a,·)`, both terms vanish, giving `P(a) = 0`. -/
theorem no_repeated_roots_of_elim_nonvanishing
    (f : PolyR n)
    (P : MvPolyR n)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (a : Fin n → ℝ)
    (hP_nz : MvPolynomial.eval a P ≠ 0) :
    ∀ y : ℝ, (specialize f a).IsRoot y →
      ¬ (specialize (Polynomial.derivative f) a).IsRoot y := by
  intro y hfy hf'y
  apply hP_nz
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP_mem
  have heq : specialize (Polynomial.C P) a = specialize (A * f + B * Polynomial.derivative f) a := by
    rw [hAB]
  have h1 : (specialize (Polynomial.C P) a).eval y = MvPolynomial.eval a P := by
    simp [specialize, Polynomial.map_C]
  have h2 : (specialize (A * f + B * Polynomial.derivative f) a).eval y =
      (specialize A a).eval y * (specialize f a).eval y +
      (specialize B a).eval y * (specialize (Polynomial.derivative f) a).eval y := by
    simp [specialize, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.eval_add, Polynomial.eval_mul]
  rw [Polynomial.IsRoot] at hfy hf'y
  have h3 := congrArg (Polynomial.eval y) heq
  rw [h1] at h3
  rw [h2, hfy, hf'y, mul_zero, mul_zero, add_zero] at h3
  exact h3

/-- If `P ∈ ⟨f, f'⟩ ∩ ℝ[x]` and `P(a) ≠ 0`, then `f(a, ·)` is separable (coprime with
its derivative). This is because the Bézout identity `C(P) = A·f + B·f'` specializes to
give `C(P(a)) ∈ ⟨f(a,·), f'(a,·)⟩`, and `P(a) ≠ 0` makes this a unit. -/
theorem separable_of_elim_nonvanishing
    (f : PolyR n)
    (P : MvPolyR n)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (a : Fin n → ℝ)
    (hP_nz : MvPolynomial.eval a P ≠ 0) :
    IsCoprime (specialize f a) (Polynomial.derivative (specialize f a)) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP_mem
  have hspec : specialize (Polynomial.C P) a =
      specialize A a * specialize f a +
      specialize B a * specialize (Polynomial.derivative f) a := by
    have : specialize (A * f + B * Polynomial.derivative f) a =
        specialize A a * specialize f a +
        specialize B a * specialize (Polynomial.derivative f) a := by
      simp [specialize, Polynomial.map_add, Polynomial.map_mul]
    rw [← this, ← hAB]
  have hCP : specialize (Polynomial.C P) a = Polynomial.C (MvPolynomial.eval a P) := by
    simp [specialize, Polynomial.map_C]
  have hder : specialize (Polynomial.derivative f) a =
      Polynomial.derivative (specialize f a) := by
    simp [specialize, Polynomial.derivative_map]
  rw [hCP, hder] at hspec
  have hunit : IsUnit (Polynomial.C (MvPolynomial.eval a P)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hP_nz)
  rw [isUnit_iff_exists_inv] at hunit
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u * specialize A a, u * specialize B a, ?_⟩
  calc (u * specialize A a) * specialize f a +
        (u * specialize B a) * Polynomial.derivative (specialize f a)
      = u * (specialize A a * specialize f a +
             specialize B a * Polynomial.derivative (specialize f a)) := by ring
    _ = u * Polynomial.C (MvPolynomial.eval a P) := by rw [← hspec]
    _ = 1 := by rw [mul_comm]; exact hu

/-! ### Delineability from separability (proved in SimpleRoots.lean) -/

/-- A polynomial that is separable (coprime with its derivative) at every point
of a connected open set is analytically delineable there, and order-invariant in each section.

This is `simple_roots_delineable'` from `Mccalum.Generalized.SimpleRoots`, which proves it
from the IFT axiom + root continuity axiom + orderFull infrastructure. -/
theorem simple_roots_delineable
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (hdeg : DegreeInvariant f S)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a))) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) :=
  simple_roots_delineable' S f hS_open hS_conn hpos hdeg hnonzero hsep

/-- Case s = r - 1 of the generalized lifting theorem.
When `S` is an open connected subset of `ℝ^{r-1}`, the theorem holds. -/
theorem lifting_generalized_open_case
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (_hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  have hP_nv := order_invariant_nowhere_vanishing_on_open S P hS_open hS_conn hP_ne hP_oi
  have hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a)) :=
    fun a ha => separable_of_elim_nonvanishing f P hP_mem a (hP_nv a ha)
  exact simple_roots_delineable S f hS_open hS_conn hpos hdeg hnonzero hsep

/-! ### Case 1 ≤ s ≤ r - 2: S has positive codimension -/

/-- Case 1 ≤ s ≤ r - 2 of the generalized lifting theorem.
When `S` is a submanifold of positive codimension, the proof uses coordinate changes,
complexification, Weierstrass preparation, the elimination ideal factorization
`P̃ = disc(h)·Q`, the order additivity lemma, and Zariski's theorem. -/
axiom lifting_generalized_codim_case
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hS_not_open : ¬ IsOpen S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S))

/-! ### Main theorem -/

/-- **Theorem 3.2.1'** (Generalized Lifting Theorem).

This generalizes `lifting_theorem` by replacing the discriminant hypothesis with an
arbitrary nonzero element `P ∈ ⟨f, ∂f/∂xᵣ⟩ ∩ R[x]` that is order-invariant on `S`.
The discriminant is one such element, so the original theorem is a special case. -/
theorem lifting_theorem_generalized'
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  by_cases hopen : IsOpen S
  · exact lifting_generalized_open_case S f hopen hS_conn hpos hsf hnonzero hdeg P hP_ne hP_mem hP_oi
  · exact lifting_generalized_codim_case S f hS_submfld hS_conn hopen hpos hsf hnonzero hdeg P hP_ne hP_mem hP_oi

#print axioms lifting_theorem_generalized'

end
