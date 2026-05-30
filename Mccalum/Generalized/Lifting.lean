import Mccalum.Prerequisites
import Mccalum.DiscrProdInvariant
import Mccalum.OrderComp
import Mccalum.SquarefreeBasis
import Mccalum.Generalized.SimpleRoots
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

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

/-! ### Order additivity lemma (Thesis Lemma 4.1) -/

section OrderAdditivity

open scoped Topology
open Filter

/-- If `h` is eventually zero near `x₀`, then `order h x₀ = ⊤`. -/
private lemma order_eq_top_of_eventuallyEq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E → ℂ) (x₀ : E) (hev : h =ᶠ[𝓝 x₀] 0) :
    order ℂ h x₀ = ⊤ := by
  rw [order_eq_top_iff (𝕜 := ℂ)]; intro n
  have := (hev.iteratedFDeriv ℂ n).self_of_nhds
  rw [this]
  rcases n with _ | n
  · ext m; simp [iteratedFDeriv_zero_apply]
  · exact congr_fun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n) (0 : ℂ)) x₀

/-- If `order ℂ f x₀ = ⊤` and `f` is analytic at `x₀`, then `f` is eventually zero. -/
private lemma eventuallyEq_zero_of_order_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ : E) (hf : AnalyticAt ℂ f x₀)
    (hord : order ℂ f x₀ = ⊤) :
    f =ᶠ[𝓝 x₀] 0 := by
  have hderiv_zero := (order_eq_top_iff (𝕜 := ℂ)).mp hord
  obtain ⟨p, r, hp⟩ := hf
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{z | z - x₀ ∈ Metric.eball 0 r}, ?_, fun z hz => ?_⟩
  · exact mem_nhds_iff.mpr ⟨_, le_refl _, Metric.isOpen_eball.preimage
      (continuous_id.sub continuous_const), by simp [Metric.mem_eball, hp.r_pos]⟩
  · have hsum := hp.hasSum_iteratedFDeriv hz
    simp only [hderiv_zero, ContinuousMultilinearMap.zero_apply, smul_zero,
      Pi.zero_apply] at hsum
    rw [show x₀ + (z - x₀) = z from by abel] at hsum
    exact hsum.unique hasSum_zero

/-- Polarization for symmetric continuous multilinear maps over ℂ: if `T` is symmetric
and vanishes on the diagonal, then `T = 0`. Proved via `iteratedFDeriv_comp_diagonal`
which gives `n! · T(v) = 0` from the diagonal vanishing. -/
private lemma symmetric_multilinear_eq_zero_of_diagonal_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (T : E [×n]→L[ℂ] ℂ)
    (hsymm : ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)), T (v ∘ σ) = T v)
    (hdiag : ∀ w : E, T (fun _ => w) = 0) :
    T = 0 := by
  ext v
  rcases n with _ | n
  · convert hdiag 0 using 1; congr 1; exact Subsingleton.elim _ _
  · have h := T.iteratedFDeriv_comp_diagonal 0 v
    have h_lhs : iteratedFDeriv ℂ (n + 1) (fun _ : E => (0 : ℂ)) 0 v = 0 := by
      simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    rw [show (fun x : E => T (fun _ => x)) = (fun _ => (0 : ℂ)) from funext hdiag,
      h_lhs] at h
    simp only [fun σ : Equiv.Perm (Fin (n + 1)) =>
      show T (fun i => v (σ i)) = T v from hsymm v σ] at h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The line restriction `t ↦ f(x₀ + t • w)` is analytic at 0 when `f` is analytic at `x₀`. -/
private lemma analyticAt_line_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ w : E) (hf : AnalyticAt ℂ f x₀) :
    AnalyticAt ℂ (fun t : ℂ => f (x₀ + t • w)) 0 := by
  apply AnalyticAt.comp (f := fun t : ℂ => x₀ + t • w)
  · simpa using hf
  · fun_prop

/-- Chain rule for line restrictions: the `k`-th iterated derivative of `t ↦ f(x₀ + t•w)`
at `t = 0` equals the `k`-th iterated Fréchet derivative of `f` at `x₀` evaluated
on the diagonal `(w, w, …, w)`. Both sides equal `k! · pₖ(w,…,w)` where `p` is
the power series of `f`. -/
private lemma iteratedDeriv_line_eq_iteratedFDeriv_diag
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ w : E) (k : ℕ)
    (hf : AnalyticAt ℂ f x₀) :
    iteratedDeriv k (fun t : ℂ => f (x₀ + t • w)) 0 =
      (iteratedFDeriv ℂ k f x₀) (fun _ => w) := by
  obtain ⟨p, r, hp⟩ := hf
  have hND := hp.iteratedFDeriv_eq_sum_of_completeSpace (n := k) (fun _ => w)
  have hp0 : HasFPowerSeriesOnBall (fun y => f (y + x₀)) p 0 r := by
    have := hp.comp_sub (-x₀)
    simp only [sub_neg_eq_add, add_neg_cancel] at this; exact this
  let L_w : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) w
  have hL_zero : L_w 0 = 0 := map_zero L_w
  have hp_line : HasFPowerSeriesOnBall (fun t => f (x₀ + t • w))
      (p.compContinuousLinearMap L_w) 0 (r / ‖L_w‖ₑ) := by
    have h1 : HasFPowerSeriesOnBall ((fun y => f (y + x₀)) ∘ L_w)
        (p.compContinuousLinearMap L_w) 0 (r / ‖L_w‖ₑ) := by
      have hp0' : HasFPowerSeriesOnBall (fun y => f (y + x₀)) p (L_w (0 : ℂ)) r := by
        rwa [show L_w (0 : ℂ) = (0 : E) from map_zero L_w]
      exact hp0'.compContinuousLinearMap
    convert h1 using 1
    ext t; simp [Function.comp_def, L_w, add_comm]
  have h1D := hp_line.iteratedFDeriv_eq_sum_of_completeSpace (n := k) (fun _ => (1 : ℂ))
  rw [show iteratedDeriv k (fun t : ℂ => f (x₀ + t • w)) 0 =
    (iteratedFDeriv ℂ k (fun t : ℂ => f (x₀ + t • w)) 0) (fun _ => (1 : ℂ)) from by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; simp]
  rw [h1D, hND]
  congr 1; ext σ
  simp [FormalMultilinearSeries.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, L_w]

/-- Vanishing order is additive for products of analytic functions:
`order(f · g) = order(f) + order(g)`. The proof reduces to the 1-variable case via
line restrictions and polarization. -/
private lemma order_mul_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (x₀ : E)
    (hf : AnalyticAt ℂ f x₀) (hg : AnalyticAt ℂ g x₀) :
    order ℂ (fun z => f z * g z) x₀ = order ℂ f x₀ + order ℂ g x₀ := by
  by_cases hf_top : order ℂ f x₀ = ⊤
  · have hfg : order ℂ (fun z => f z * g z) x₀ = ⊤ :=
      order_eq_top_of_eventuallyEq_zero _ x₀ <| by
        filter_upwards [eventuallyEq_zero_of_order_eq_top f x₀ hf hf_top] with z hz
        simp [hz]
    simp [hfg, hf_top]
  by_cases hg_top : order ℂ g x₀ = ⊤
  · have hfg : order ℂ (fun z => f z * g z) x₀ = ⊤ :=
      order_eq_top_of_eventuallyEq_zero _ x₀ <| by
        filter_upwards [eventuallyEq_zero_of_order_eq_top g x₀ hg hg_top] with z hz
        simp [hz]
    simp [hfg, hg_top]
  -- Both orders are finite: extract natural numbers m, n
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hf_top
  obtain ⟨nn, hnn⟩ := ENat.ne_top_iff_exists.mp hg_top
  rw [← hm, ← hnn, ← ENat.coe_add]
  -- Characterize: iteratedFDeriv vanishes below order, nonzero at order
  have hf_below : ∀ j < m, iteratedFDeriv ℂ j f x₀ = 0 := fun j hj =>
    iteratedFDeriv_eq_zero_of_lt_order (by rw [← hm]; exact_mod_cast hj)
  have hf_at : iteratedFDeriv ℂ m f x₀ ≠ 0 :=
    ((order_eq_natCast_iff (𝕜 := ℂ) (n := m)).mp hm.symm).2
  have hg_below : ∀ j < nn, iteratedFDeriv ℂ j g x₀ = 0 := fun j hj =>
    iteratedFDeriv_eq_zero_of_lt_order (by rw [← hnn]; exact_mod_cast hj)
  have hg_at : iteratedFDeriv ℂ nn g x₀ ≠ 0 :=
    ((order_eq_natCast_iff (𝕜 := ℂ) (n := nn)).mp hnn.symm).2
  -- Diagonal vanishing for f and g
  have hf_diag : ∀ j < m, ∀ w : E, (iteratedFDeriv ℂ j f x₀) (fun _ => w) = 0 :=
    fun j hj w => by simp [hf_below j hj]
  have hg_diag : ∀ j < nn, ∀ w : E, (iteratedFDeriv ℂ j g x₀) (fun _ => w) = 0 :=
    fun j hj w => by simp [hg_below j hj]
  -- By polarization: ∃ w₀ with diagonal nonzero at order
  have hf_diag_ne : ∃ w₀ : E, (iteratedFDeriv ℂ m f x₀) (fun _ => w₀) ≠ 0 := by
    by_contra h; push_neg at h
    exact hf_at (symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hf.contDiffAt.iteratedFDeriv_comp_perm v σ) h)
  have hg_diag_ne : ∃ w₀ : E, (iteratedFDeriv ℂ nn g x₀) (fun _ => w₀) ≠ 0 := by
    by_contra h; push_neg at h
    exact hg_at (symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hg.contDiffAt.iteratedFDeriv_comp_perm v σ) h)
  -- Line restriction orders
  have hf_line : ∀ w, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
    intro w
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction f x₀ w hf)]
    exact fun i hi => by rw [iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w i hf]; exact hf_diag i hi w
  have hg_line : ∀ w, (nn : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 := by
    intro w
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction g x₀ w hg)]
    exact fun i hi => by rw [iteratedDeriv_line_eq_iteratedFDeriv_diag g x₀ w i hg]; exact hg_diag i hi w
  -- Analyticity of the product
  have hfg : AnalyticAt ℂ (fun z => f z * g z) x₀ := hf.mul hg
  -- ≥ direction: order(fg) ≥ m + nn via 1D analyticOrderAt_mul + polarization
  have h_ge : (↑(m + nn) : ℕ∞) ≤ order ℂ (fun z => f z * g z) x₀ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have hjlt : j < m + nn := by exact_mod_cast (hj ▸ hlt : (↑j : ℕ∞) < ↑(m + nn))
    have hj_ne := ((order_eq_natCast_iff (𝕜 := ℂ) (n := j)).mp hj.symm).2
    apply hj_ne
    apply symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hfg.contDiffAt.iteratedFDeriv_comp_perm v σ)
    intro w
    rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag _ x₀ w j hfg]
    have h_anal := analyticAt_line_restriction (fun z => f z * g z) x₀ w hfg
    have h_fg_ord : ↑(m + nn) ≤
        analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 := by
      calc (↑(m + nn) : ℕ∞) = ↑m + ↑nn := by push_cast; ring
        _ ≤ analyticOrderAt (fun t => f (x₀ + t • w)) 0 +
            analyticOrderAt (fun t => g (x₀ + t • w)) 0 := add_le_add (hf_line w) (hg_line w)
        _ = analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 :=
            (analyticOrderAt_mul (analyticAt_line_restriction f x₀ w hf)
              (analyticAt_line_restriction g x₀ w hg)).symm
    exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero h_anal).mp h_fg_ord) j hjlt
  -- ≤ direction: find w with both T_f(w,...,w) ≠ 0 and T_g(w,...,w) ≠ 0
  have h_le : order ℂ (fun z => f z * g z) x₀ ≤ ↑(m + nn) := by
    suffices h : iteratedFDeriv ℂ (m + nn) (fun z => f z * g z) x₀ ≠ 0 by
      have hex : ∃ n, iteratedFDeriv ℂ n (fun z => f z * g z) x₀ ≠ 0 := ⟨m + nn, h⟩
      unfold order; rw [dif_pos hex]; exact_mod_cast Nat.find_min' hex h
    obtain ⟨v₀, hv₀⟩ := hf_diag_ne
    obtain ⟨w₀, hw₀⟩ := hg_diag_ne
    -- Find w with both T_f(fun _ => w) ≠ 0 and T_g(fun _ => w) ≠ 0
    -- (using 1D analytic argument on the line v₀ + t•w₀)
    obtain ⟨w, hw_f, hw_g⟩ : ∃ w : E,
        (iteratedFDeriv ℂ m f x₀) (fun _ => w) ≠ 0 ∧
        (iteratedFDeriv ℂ nn g x₀) (fun _ => w) ≠ 0 := by
      -- D_g(w) := T_g(w,...,w) is analytic (multilinear map composed with diagonal)
      have hDg_anal : AnalyticAt ℂ
          (fun w : E => (iteratedFDeriv ℂ nn g x₀) (fun _ => w)) v₀ :=
        (iteratedFDeriv ℂ nn g x₀).analyticAt.comp
          (AnalyticAt.pi (fun _ : Fin nn => analyticAt_id))
      -- ψ(t) := T_g(v₀+t•w₀,...) is analytic at 0
      have hψ_anal := analyticAt_line_restriction
        (fun w => (iteratedFDeriv ℂ nn g x₀) (fun _ => w)) v₀ w₀ hDg_anal
      -- nn-th derivative of ψ at 0 is nn! • T_g(w₀,...,w₀) ≠ 0
      have hψ_deriv : iteratedDeriv nn (fun t : ℂ =>
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 ≠ 0 := by
        rw [iteratedDeriv_line_eq_iteratedFDeriv_diag _ v₀ w₀ nn hDg_anal,
            (iteratedFDeriv ℂ nn g x₀).iteratedFDeriv_comp_diagonal v₀ (fun _ => w₀)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero nn)) hw₀
      -- analyticOrderAt ψ 0 ≠ ⊤ (since nn-th derivative is nonzero)
      have hψ_ne_top : analyticOrderAt (fun t : ℂ =>
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 ≠ ⊤ := by
        intro h_top; apply hψ_deriv
        have h_le : ↑(nn + 1) ≤ analyticOrderAt (fun t : ℂ =>
            (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 := by
          rw [h_top]; exact le_top
        exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hψ_anal).mp h_le nn (by omega)
      -- ∃ᶠ t near 0, T_g(v₀+t•w₀,...) ≠ 0
      have hψ_freq : ∃ᶠ t in 𝓝 (0 : ℂ),
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀) ≠ 0 :=
        Filter.not_eventually.mp (analyticOrderAt_eq_top.not.mp hψ_ne_top)
      -- ∀ᶠ t near 0, T_f(v₀+t•w₀,...) ≠ 0 (continuity + nonvanishing at 0)
      have hφ_ev : ∀ᶠ t in 𝓝 (0 : ℂ),
          (iteratedFDeriv ℂ m f x₀) (fun _ => v₀ + t • w₀) ≠ 0 := by
        refine ContinuousAt.eventually_ne ?_ ?_
        · exact (iteratedFDeriv ℂ m f x₀).cont.continuousAt.comp (by fun_prop)
        · simpa using hv₀
      -- Combine: ∃ t with both nonzero
      obtain ⟨t, hψt, hφt⟩ := (hψ_freq.and_eventually hφ_ev).exists
      exact ⟨v₀ + t • w₀, hφt, hψt⟩
    -- w gives exact analyticOrderAt: f_w has order m, g_w has order nn
    have hf_w_eq : analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 = ↑m := by
      apply le_antisymm
      · by_contra hgt; push_neg at hgt
        have h_succ : (↑(m + 1) : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
          rwa [show (↑(m + 1) : ℕ∞) = ↑m + 1 from by push_cast; ring,
            ENat.add_one_le_iff (ENat.coe_ne_top m)]
        apply hw_f
        rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w m hf]
        exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction f x₀ w hf)).mp h_succ) m (by omega)
      · exact hf_line w
    have hg_w_eq : analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 = ↑nn := by
      apply le_antisymm
      · by_contra hgt; push_neg at hgt
        have h_succ : (↑(nn + 1) : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 := by
          rwa [show (↑(nn + 1) : ℕ∞) = ↑nn + 1 from by push_cast; ring,
            ENat.add_one_le_iff (ENat.coe_ne_top nn)]
        apply hw_g
        rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag g x₀ w nn hg]
        exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction g x₀ w hg)).mp h_succ) nn (by omega)
      · exact hg_line w
    -- Product has analyticOrderAt = m + nn
    have hfg_w_eq : analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 =
        ↑(m + nn) := by
      calc analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0
          = analyticOrderAt (fun t => f (x₀ + t • w)) 0 +
            analyticOrderAt (fun t => g (x₀ + t • w)) 0 :=
            analyticOrderAt_mul (analyticAt_line_restriction f x₀ w hf)
              (analyticAt_line_restriction g x₀ w hg)
        _ = ↑m + ↑nn := by rw [hf_w_eq, hg_w_eq]
        _ = ↑(m + nn) := by push_cast; ring
    -- The (m+nn)-th iteratedDeriv of the line restriction is nonzero
    intro h_eq
    have h_diag_zero : (iteratedFDeriv ℂ (m + nn) (fun z => f z * g z) x₀) (fun _ => w) = 0 :=
      by simp [h_eq]
    rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag _ x₀ w _ hfg] at h_diag_zero
    -- But analyticOrderAt = m+nn means iteratedDeriv (m+nn) ≠ 0
    have h_below : ∀ i < m + nn + 1,
        iteratedDeriv i (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 = 0 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction _ x₀ w hfg)).mp (le_of_eq hfg_w_eq.symm)) i hi'
      · exact hi' ▸ h_diag_zero
    have h_succ := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction _ x₀ w hfg)).mpr h_below
    rw [hfg_w_eq] at h_succ
    exact absurd (by exact_mod_cast h_succ : m + nn + 1 ≤ m + nn) (by omega)
  exact le_antisymm h_le h_ge

/-- Identity theorem for multi-variable analytic functions: if `f` is analytic on a
connected open set and not identically zero, then `f` has finite vanishing order everywhere.

The proof shows `{z ∈ U : order f z = ⊤}` is clopen: closed because it is
`⋂_n {iteratedFDeriv n f = 0}`, and open because at a point of infinite order the
power series is identically zero, so `f = 0` on a ball, hence all derivatives vanish
throughout that ball. -/
private lemma order_ne_top_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU_open : IsOpen U) (hU_conn : IsConnected U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, order ℂ f z ≠ ⊤ := by
  -- Contrapositive: if order = ⊤ somewhere, f = 0 on all of U.
  by_contra hpush
  push_neg at hpush
  obtain ⟨z₀, hz₀, hord⟩ := hpush
  -- order = ⊤ means all iteratedFDeriv vanish at z₀
  have hderiv_zero : ∀ n, iteratedFDeriv ℂ n f z₀ = 0 :=
    (order_eq_top_iff (𝕜 := ℂ)).mp hord
  -- f is analytic at z₀, so it has a convergent power series
  obtain ⟨p, r, hp⟩ := hf z₀ hz₀
  -- All terms of ∑ (n!)⁻¹ • iteratedFDeriv n f z₀ (fun _ => y) vanish
  -- so the sum (= f(z₀ + y)) is 0 for y near 0
  have hf_zero : f =ᶠ[𝓝 z₀] 0 := by
    rw [eventuallyEq_iff_exists_mem]
    refine ⟨{z | z - z₀ ∈ Metric.eball 0 r}, ?_, fun z hz => ?_⟩
    · apply mem_nhds_iff.mpr
      refine ⟨{z | z - z₀ ∈ Metric.eball 0 r}, le_refl _, ?_, ?_⟩
      · exact Metric.isOpen_eball.preimage (continuous_id.sub continuous_const)
      · simp [Metric.mem_eball, hp.r_pos]
    · have hsum := hp.hasSum_iteratedFDeriv hz
      simp only [hderiv_zero, ContinuousMultilinearMap.zero_apply, smul_zero,
        Pi.zero_apply] at hsum
      rw [show z₀ + (z - z₀) = z from by abel] at hsum
      exact hsum.unique hasSum_zero
  -- By identity principle: f = 0 on all of U
  have hf_eq : Set.EqOn f 0 U :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_conn.isPreconnected hz₀ hf_zero
  -- This contradicts the existence of z with f z ≠ 0
  obtain ⟨z, hzU, hfz⟩ := hne
  exact hfz (hf_eq hzU)

/-- Upper semi-continuity of vanishing order: `{z ∈ U | order f z ≤ n}` is open
for `f` analytic on open `U`. At a point where `order ≤ n`, some `iteratedFDeriv k f`
is nonzero. By continuity of `iteratedFDeriv` (analytic ⟹ C^∞), this persists nearby. -/
private lemma isOpen_order_le_inter
    (s : ℕ) (U : Set (Fin s → ℂ)) (hU_open : IsOpen U)
    (f : (Fin s → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f U) (n : ℕ∞) :
    IsOpen {z ∈ U | order ℂ f z ≤ n} := by
  -- Handle n = ⊤: {order ≤ ⊤} = U, which is open
  rcases eq_or_ne n ⊤ with rfl | hn_ne
  · convert hU_open using 1; ext z; simp [Set.mem_sep_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro z₀ ⟨hz₀U, hz₀_le⟩
  -- order ℂ f z₀ ≤ n < ⊤ means order is finite
  have hfin : ∃ m, iteratedFDeriv ℂ m f z₀ ≠ 0 := by
    rw [order] at hz₀_le
    split_ifs at hz₀_le with h
    · exact h
    · exact absurd (le_antisymm hz₀_le le_top).symm hn_ne
  set k := Nat.find hfin
  have hk_ne : iteratedFDeriv ℂ k f z₀ ≠ 0 := Nat.find_spec hfin
  have hk_le : (k : ℕ∞) ≤ n := by
    have hord : order ℂ f z₀ = ↑k := by rw [order, dif_pos hfin]
    rw [← hord]; exact hz₀_le
  -- U ∩ {iteratedFDeriv k f ≠ 0} is open and contains z₀
  have hcont : ContinuousOn (iteratedFDeriv ℂ k f) U :=
    (hf.iteratedFDeriv_of_isOpen hU_open k).continuousOn
  set W := U ∩ (iteratedFDeriv ℂ k f) ⁻¹' {x | x ≠ 0}
  have hW_open : IsOpen W := hcont.isOpen_inter_preimage hU_open isOpen_ne
  have hW_sub : W ⊆ {z ∈ U | order ℂ f z ≤ n} := by
    intro z ⟨hzU, hzk⟩
    refine ⟨hzU, le_trans ?_ hk_le⟩
    rw [order, dif_pos ⟨k, hzk⟩]
    exact Nat.cast_le.mpr (Nat.find_min' _ hzk)
  exact ⟨W, hW_sub, hW_open, hz₀U, hk_ne⟩

/-- The set `{z ∈ U | order f z < b}` is open for `f` analytic on open `U`. -/
private lemma isOpen_order_lt_inter
    (s : ℕ) (U : Set (Fin s → ℂ)) (hU_open : IsOpen U)
    (f : (Fin s → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f U) (b : ℕ∞) :
    IsOpen {z ∈ U | order ℂ f z < b} := by
  -- {order < b} = ⋃ (n : ℕ) (hn : ↑n < b), {order ≤ n} (since order takes values in ℕ∞)
  -- But more directly: at z₀ with order < b, order(z₀) = k for some k < b.
  -- Then {order ≤ k} ∩ U is open (isOpen_order_le_inter) and z₀ ∈ it ⊆ {order < b}.
  apply isOpen_iff_forall_mem_open.mpr
  intro z₀ ⟨hz₀U, hz₀_lt⟩
  have hfin : order ℂ f z₀ ≠ ⊤ := ne_top_of_lt hz₀_lt
  set k := (order ℂ f z₀).toNat
  have hk : order ℂ f z₀ = ↑k := (ENat.coe_toNat hfin).symm
  refine ⟨{z ∈ U | order ℂ f z ≤ ↑k}, fun z ⟨hzU, hle⟩ => ⟨hzU, lt_of_le_of_lt hle ?_⟩,
         isOpen_order_le_inter s U hU_open f hf ↑k, hz₀U, hk ▸ le_refl _⟩
  rw [← hk]; exact hz₀_lt

/-- **Order additivity lemma** (Thesis Lemma 4.1).

On a connected open subset of `ℂˢ`, if two holomorphic functions `f` and `g` (both not
identically zero) have the property that `f · g` has constant vanishing order, then `f`
and `g` each individually have constant vanishing order.

Proved from `order_mul_analytic` (order of product = sum of orders) via `IsPreconnected`:
set `A = {order(f) ≤ a}` and `B = {order(g) < b}` where `a + b = c` (the constant).
Both are open; `U ⊆ A ∪ B` (from the sum constraint); `A ∩ B ∩ U = ∅` (any point in
both satisfies `order(f) + order(g) < c`, contradicting the constraint). Connectivity
forces `U ∩ B = ∅`, so `order(g) ≥ b` everywhere. Symmetrically `order(f) ≥ a`. -/
theorem order_additivity_holomorphic
    (s : ℕ) (U : Set (Fin s → ℂ))
    (hU_open : IsOpen U) (hU_conn : IsConnected U)
    (f g : (Fin s → ℂ) → ℂ)
    (hf_an : AnalyticOnNhd ℂ f U) (hg_an : AnalyticOnNhd ℂ g U)
    (hf_ne : ∃ z ∈ U, f z ≠ 0) (hg_ne : ∃ z ∈ U, g z ≠ 0)
    (hfg_const : ∀ z₁ ∈ U, ∀ z₂ ∈ U,
      order ℂ (fun z => f z * g z) z₁ = order ℂ (fun z => f z * g z) z₂) :
    (∀ z₁ ∈ U, ∀ z₂ ∈ U, order ℂ f z₁ = order ℂ f z₂) ∧
    (∀ z₁ ∈ U, ∀ z₂ ∈ U, order ℂ g z₁ = order ℂ g z₂) := by
  -- Step 1: Finite order everywhere (identity theorem)
  have hf_fin : ∀ z ∈ U, order ℂ f z ≠ ⊤ :=
    order_ne_top_of_ne_zero U hU_open hU_conn f hf_an hf_ne
  have hg_fin : ∀ z ∈ U, order ℂ g z ≠ ⊤ :=
    order_ne_top_of_ne_zero U hU_open hU_conn g hg_an hg_ne
  -- Step 2: order(f)(z) + order(g)(z) = c for all z ∈ U (order additivity for products)
  obtain ⟨z₀, hz₀⟩ := hU_conn.nonempty
  set c := order ℂ (fun w => f w * g w) z₀
  have hsum_eq : ∀ z ∈ U, order ℂ f z + order ℂ g z = c := by
    intro z hz
    rw [← order_mul_analytic f g z (hf_an z hz) (hg_an z hz)]
    exact hfg_const z hz z₀ hz₀
  set a := order ℂ f z₀
  set b := order ℂ g z₀
  have hab : a + b = c := hsum_eq z₀ hz₀
  have ha_ne : a ≠ ⊤ := hf_fin z₀ hz₀
  have hb_ne : b ≠ ⊤ := hg_fin z₀ hz₀
  -- Step 3: Connectivity argument using IsPreconnected
  -- A = {z ∈ U | order(f) ≤ a} and B = {z ∈ U | order(g) < b} are open.
  -- They cover U (from sum constraint: order(f) > a ⟹ order(g) < b).
  -- Their intersection in U is empty (order(f) ≤ a ∧ order(g) < b ⟹ sum < c).
  -- So by connectivity, U ∩ B = ∅, i.e., order(g) ≥ b on U. Symmetrically for f.
  -- The key properties of ENat (additive cancellation for ≠ ⊤) give exact bounds.
  -- Deferred: ENat bookkeeping for the connectivity argument
  -- Helper: from sum constraint, order(f) > a at z implies order(g) < b at z
  have sum_transfer_fg : ∀ z ∈ U, a < order ℂ f z → order ℂ g z < b := by
    intro z hz hlt
    have hsz := hsum_eq z hz; rw [← hab] at hsz
    -- a < order(f)(z), so a + order(g)(z) < order(f)(z) + order(g)(z) = a + b
    have h1 : a + order ℂ g z < order ℂ f z + order ℂ g z :=
      (ENat.add_lt_add_iff_right (hg_fin z hz)).mpr hlt
    rw [hsz] at h1  -- a + order(g)(z) < a + b
    exact (ENat.add_lt_add_iff_left ha_ne).mp h1
  have sum_transfer_gf : ∀ z ∈ U, b < order ℂ g z → order ℂ f z < a := by
    intro z hz hlt
    have hsz := hsum_eq z hz; rw [← hab] at hsz
    have h1 : order ℂ f z + b < order ℂ f z + order ℂ g z :=
      (ENat.add_lt_add_iff_left (hf_fin z hz)).mpr hlt
    rw [hsz] at h1
    exact (ENat.add_lt_add_iff_right hb_ne).mp h1
  have hf_le : ∀ z ∈ U, order ℂ f z ≤ a := by
    by_contra hpush; push_neg at hpush
    obtain ⟨z₁, hz₁, hlt⟩ := hpush
    set A' := {z ∈ U | order ℂ f z ≤ a}
    set B' := {z ∈ U | order ℂ g z < b}
    -- A' and B' are open, cover U, have empty intersection in U
    have hA'_open := isOpen_order_le_inter s U hU_open f hf_an a
    have hB'_open := isOpen_order_lt_inter s U hU_open g hg_an b
    have hcov : U ⊆ A' ∪ B' := by
      intro z hz
      by_cases h : order ℂ f z ≤ a
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, sum_transfer_fg z hz (not_le.mp h)⟩
    have hdisj : ¬(U ∩ (A' ∩ B')).Nonempty := by
      rintro ⟨z, hzU, ⟨_, hle_a⟩, _, hlt_b⟩
      have hsz := hsum_eq z hzU; rw [← hab] at hsz
      have : order ℂ f z + order ℂ g z < a + b :=
        lt_of_le_of_lt ((ENat.add_le_add_iff_right (hg_fin z hzU)).mpr hle_a)
          ((ENat.add_lt_add_iff_left ha_ne).mpr hlt_b)
      exact absurd hsz (ne_of_lt this)
    exact hdisj (hU_conn.isPreconnected A' B' hA'_open hB'_open hcov
      ⟨z₀, hz₀, hz₀, le_refl a⟩ ⟨z₁, hz₁, hz₁, sum_transfer_fg z₁ hz₁ hlt⟩)
  have hg_le : ∀ z ∈ U, order ℂ g z ≤ b := by
    by_contra hpush; push_neg at hpush
    obtain ⟨z₁, hz₁, hlt⟩ := hpush
    set A' := {z ∈ U | order ℂ g z ≤ b}
    set B' := {z ∈ U | order ℂ f z < a}
    have hA'_open := isOpen_order_le_inter s U hU_open g hg_an b
    have hB'_open := isOpen_order_lt_inter s U hU_open f hf_an a
    have hcov : U ⊆ A' ∪ B' := by
      intro z hz
      by_cases h : order ℂ g z ≤ b
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, sum_transfer_gf z hz (not_le.mp h)⟩
    have hdisj : ¬(U ∩ (A' ∩ B')).Nonempty := by
      rintro ⟨z, hzU, ⟨_, hle_b⟩, _, hlt_a⟩
      have hsz := hsum_eq z hzU; rw [← hab] at hsz
      have : order ℂ f z + order ℂ g z < a + b :=
        lt_of_lt_of_le ((ENat.add_lt_add_iff_right (hg_fin z hzU)).mpr hlt_a)
          ((ENat.add_le_add_iff_left ha_ne).mpr hle_b)
      exact absurd hsz (ne_of_lt this)
    exact hdisj (hU_conn.isPreconnected A' B' hA'_open hB'_open hcov
      ⟨z₀, hz₀, hz₀, le_refl b⟩ ⟨z₁, hz₁, hz₁, sum_transfer_gf z₁ hz₁ hlt⟩)
  -- Step 4: From f ≤ a, g ≤ b, f + g = a + b: equality.
  -- f(z) + g(z) = a + b and f(z) ≤ a and g(z) ≤ b forces f(z) = a, g(z) = b.
  have hf_eq : ∀ z ∈ U, order ℂ f z = a := by
    intro z hz
    have hle := hf_le z hz
    have hge : a ≤ order ℂ f z := by
      -- From g(z) ≤ b: a + g(z) ≤ a + b = f(z) + g(z), so a ≤ f(z)
      have hsz := hsum_eq z hz
      rw [← hab] at hsz
      exact (ENat.add_le_add_iff_right (hg_fin z hz)).mp (hsz ▸ (ENat.add_le_add_iff_left ha_ne).mpr (hg_le z hz))
    exact le_antisymm hle hge
  have hg_eq : ∀ z ∈ U, order ℂ g z = b := by
    intro z hz
    have hle := hg_le z hz
    have hge : b ≤ order ℂ g z := by
      -- From f(z) ≤ a: f(z) + b ≤ a + b = f(z) + g(z), so b ≤ g(z)
      have hsz := hsum_eq z hz
      rw [← hab] at hsz
      exact (ENat.add_le_add_iff_left (hf_fin z hz)).mp (hsz ▸ (ENat.add_le_add_iff_right hb_ne).mpr (hf_le z hz))
    exact le_antisymm hle hge
  exact ⟨fun z₁ hz₁ z₂ hz₂ => by rw [hf_eq z₁ hz₁, hf_eq z₂ hz₂],
         fun z₁ hz₁ z₂ hz₂ => by rw [hg_eq z₁ hz₁, hg_eq z₂ hz₂]⟩

end OrderAdditivity

/-! ### Norm identity for monic polynomials -/

section NormResultant

/-- Norm factorization: `norm K (mk ((X - C a) * h') g) = eval a g * norm K (mk h' g)` for
monic h'. Uses `LinearMap.det_eq_det_mul_det` on the kernel of the projection
`AdjoinRoot ((X-C a) * h') → AdjoinRoot h'`, which is 1-dimensional with scalar action g(a). -/
private lemma norm_mk_mul_X_sub_C {K : Type*} [Field K] (a : K) (h' g : Polynomial K)
    (hm' : h'.Monic) :
    Algebra.norm K (AdjoinRoot.mk ((Polynomial.X - Polynomial.C a) * h') g) =
      Polynomial.eval a g * Algebra.norm K (AdjoinRoot.mk h' g) := by
  set h := (Polynomial.X - Polynomial.C a) * h' with h_def
  have hm : h.Monic := (Polynomial.monic_X_sub_C a).mul hm'
  haveI := hm.finite_adjoinRoot (R := K)
  -- The projection π : AdjoinRoot h →ₐ[K] AdjoinRoot h'
  have heval : Polynomial.aeval (AdjoinRoot.root h') h = 0 := by
    rw [AdjoinRoot.aeval_eq, h_def, map_mul, AdjoinRoot.mk_self, mul_zero]
  let π : AdjoinRoot h →ₐ[K] AdjoinRoot h' := AdjoinRoot.liftHom h (AdjoinRoot.root h') heval
  have hπ_mk (p : Polynomial K) : π (AdjoinRoot.mk h p) = AdjoinRoot.mk h' p := by
    show AdjoinRoot.liftHom h (AdjoinRoot.root h') heval (AdjoinRoot.mk h p) = _
    exact AdjoinRoot.aeval_eq p
  -- Left multiplication by mk h g, and its kernel
  let e : AdjoinRoot h →ₗ[K] AdjoinRoot h :=
    (Algebra.lmul K (AdjoinRoot h)) (AdjoinRoot.mk h g)
  let W : Submodule K (AdjoinRoot h) := π.toLinearMap.ker
  have he : W ≤ W.comap e := by
    intro w hw
    simp only [Submodule.mem_comap, W, LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hw ⊢
    show π (AdjoinRoot.mk h g * w) = 0
    rw [map_mul, hw, mul_zero]
  -- Unfold norm to det and apply det factorization
  simp only [Algebra.norm_apply]
  show e.det = Polynomial.eval a g *
    (Algebra.lmul K (AdjoinRoot h') (AdjoinRoot.mk h' g)).det
  rw [LinearMap.det_eq_det_mul_det W e he]
  -- π is surjective (shared between both goals)
  have hπ_surj : Function.Surjective π.toLinearMap := by
    intro y; obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨AdjoinRoot.mk h p, hπ_mk p⟩
  congr 1
  · -- det(e|_W) = eval a g
    -- Convert he to explicit form for LinearMap.restrict
    have he' : ∀ x ∈ W, e x ∈ W := fun x hx => he hx
    change (e.restrict he').det = Polynomial.eval a g
    -- e acts as scalar (eval a g) on W
    have hscalar : e.restrict he' = (Polynomial.eval a g) • LinearMap.id := by
      ext ⟨w, hw⟩
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
        SetLike.val_smul, e, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
      rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul]
      -- Decompose w as mk h f before using map_sub/map_mul
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective w
      change (AdjoinRoot.mk h g - AdjoinRoot.mk h
        (Polynomial.C (Polynomial.eval a g))) * AdjoinRoot.mk h f = 0
      rw [← map_sub, ← map_mul]
      have hmk_zero : AdjoinRoot.mk h' f = 0 := by
        have := LinearMap.mem_ker.mp hw
        rwa [AlgHom.toLinearMap_apply, hπ_mk] at this
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hmk_zero
      have hroot : Polynomial.IsRoot (g - Polynomial.C (Polynomial.eval a g)) a := by
        simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
      obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      exact AdjoinRoot.mk_eq_zero.mpr ⟨r * q, by rw [hr, h_def]; ring⟩
    -- finrank K W = 1 by rank-nullity
    have hfr_W : Module.finrank K ↥W = 1 := by
      have h1 := Submodule.finrank_quotient_add_finrank W
      have h2 : Module.finrank K (AdjoinRoot h ⧸ W) = h'.natDegree := by
        rw [LinearEquiv.finrank_eq (π.toLinearMap.quotKerEquivOfSurjective hπ_surj)]
        exact (AdjoinRoot.powerBasis hm'.ne_zero).finrank
      have h3 : Module.finrank K (AdjoinRoot h) = h.natDegree :=
        (AdjoinRoot.powerBasis hm.ne_zero).finrank
      have h4 : h.natDegree = h'.natDegree + 1 := by
        rw [h_def, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero hm'.ne_zero,
          Polynomial.natDegree_X_sub_C, add_comm]
      omega
    rw [hscalar, LinearMap.det_smul, LinearMap.det_id, mul_one, hfr_W, pow_one]
  · -- det(quotient map) = norm K (mk h' g)
    let φ := π.toLinearMap.quotKerEquivOfSurjective hπ_surj
    -- Show mapQ = φ⁻¹ ∘ lmul ∘ φ by quotient induction
    have hmapQ : W.mapQ W e he =
        φ.symm.toLinearMap ∘ₗ (Algebra.lmul K (AdjoinRoot h') (AdjoinRoot.mk h' g)) ∘ₗ
          φ.toLinearMap := by
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W q
      simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, Algebra.coe_lmul_eq_mul]
      change Submodule.Quotient.mk (e x) =
        φ.symm ((LinearMap.mul K (AdjoinRoot h') ((AdjoinRoot.mk h') g))
          (φ (Submodule.Quotient.mk x)))
      rw [LinearEquiv.eq_symm_apply]
      simp only [φ, LinearMap.quotKerEquivOfSurjective_apply_mk, AlgHom.toLinearMap_apply,
        e, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', map_mul, hπ_mk]
    rw [hmapQ]
    exact LinearMap.det_conj _ φ.symm

open Polynomial AdjoinRoot Algebra in
private lemma norm_eq_prod_eval_of_monic_splits {K : Type*} [Field K]
    (s : Multiset K) (g : Polynomial K) :
    Algebra.norm K (AdjoinRoot.mk ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod) g) =
    (s.map (Polynomial.eval · g)).prod := by
  induction s using Multiset.induction with
  | empty =>
    have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (0 : Multiset K)).prod = (1 : Polynomial K) := by
      rw [Multiset.map_zero, Multiset.prod_zero]
    rw [heq, Multiset.map_zero, Multiset.prod_zero]
    haveI : Subsingleton (AdjoinRoot (1 : Polynomial K)) := by
      rw [show (1 : Polynomial K) = Polynomial.C 1 from Polynomial.C_1.symm,
        AdjoinRoot, Ideal.span_singleton_eq_top.mpr (isUnit_C.mpr isUnit_one)]
      infer_instance
    rw [show mk (1 : Polynomial K) g = 1 from Subsingleton.elim _ _, map_one]
  | cons a s ih =>
    have hm' : ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod).Monic :=
      monic_multiset_prod_of_monic s _ (fun a _ => monic_X_sub_C a)
    have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (a ::ₘ s)).prod =
        (Polynomial.X - Polynomial.C a) *
          (s.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [heq, norm_mk_mul_X_sub_C a _ g hm', ih, Multiset.map_cons, Multiset.prod_cons]

end NormResultant

/-- The algebra norm on `AdjoinRoot h` commutes with ring maps, for monic `h`.
The proof shows that the left multiplication matrix entries (coefficients of `g * X^j %ₘ h`)
commute with ring maps via `map_modByMonic`. -/
private lemma norm_adjoinRoot_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (h g : Polynomial R) (hm : h.Monic) :
    φ (Algebra.norm R (AdjoinRoot.mk h g)) =
    Algebra.norm S (AdjoinRoot.mk (h.map φ) (g.map φ)) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  have hnd : (h.map φ).natDegree = h.natDegree := hm.natDegree_map φ
  rw [Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasis' hm).basis, RingHom.map_det]
  conv_rhs =>
    rw [Algebra.norm_eq_matrix_det ((AdjoinRoot.powerBasis' (hm.map φ)).basis.reindex
      (finCongr hnd))]
  congr 1; ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, finCongr_symm]
  simp only [(AdjoinRoot.powerBasis' hm).basis_eq_pow,
    (AdjoinRoot.powerBasis' (hm.map φ)).basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  -- Reduce repr to modByMonicHom coeff
  change φ ((AdjoinRoot.powerBasisAux' hm).repr _ _) =
    (AdjoinRoot.powerBasisAux' (hm.map φ)).repr _ _
  simp only [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  -- Simplify mk * root^j using root = mk X
  simp only [AdjoinRoot.root, ← map_pow (AdjoinRoot.mk h), ← map_mul (AdjoinRoot.mk h),
    ← map_pow (AdjoinRoot.mk (h.map φ)), ← map_mul (AdjoinRoot.mk (h.map φ))]
  simp only [AdjoinRoot.modByMonicHom_mk]
  rw [← Polynomial.coeff_map φ, Polynomial.map_modByMonic _ hm,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  simp only [finCongr_apply, Fin.val_cast]

/-- **Norm–resultant identity for monic polynomials** (Thesis Lemma 5.1).

For `h` monic of degree `m` over a commutative ring `R`, the algebra norm of `ḡ` in
`R[z]/(h)` equals `Res(h, g)`.

The proof uses a universal coefficient approach: reduce to the case where the base ring
is a field and `h` splits into linear factors (via `induction_of_Splits`), then use
`resultant_eq_prod_eval` and the norm decomposition for products of linear factors. -/
theorem norm_eq_resultant_monic
    (R : Type*) [CommRing R]
    (h g : Polynomial R) (hm : h.Monic) :
    Algebra.norm R (AdjoinRoot.mk h g) = Polynomial.resultant h g := by
  revert hm g
  induction h using Polynomial.induction_of_Splits_of_injective_of_surjective with
  | Splits K h hh =>
    intro g hm
    -- Both sides equal (h.roots.map g.eval).prod
    have hres : Polynomial.resultant h g = (h.roots.map g.eval).prod := by
      have := Polynomial.resultant_eq_prod_eval h g g.natDegree le_rfl hh
      rwa [hm.leadingCoeff, one_pow, one_mul] at this
    rw [hres]
    conv_lhs => rw [hh.eq_prod_roots_of_monic hm]
    exact norm_eq_prod_eval_of_monic_splits h.roots g
  | injective R' S' φ hφ h IH =>
    intro g hm
    have := IH (g.map φ) (hm.map φ)
    rw [Polynomial.resultant_map_map,
      Polynomial.natDegree_map_eq_of_injective hφ h,
      Polynomial.natDegree_map_eq_of_injective hφ g,
      ← norm_adjoinRoot_map φ h g hm] at this
    exact hφ this
  | surjective R' S' φ hφ h IH =>
    intro g hm
    obtain ⟨h', hh', ndh, hh'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.map_surjective φ hφ h) hm
    obtain ⟨g', hg', eg⟩ := Polynomial.mem_lifts_and_degree_eq
      (Polynomial.map_surjective φ hφ g)
    have hndh : (Polynomial.map φ h').natDegree = h'.natDegree :=
      (congr_arg Polynomial.natDegree hh').trans ndh.symm
    have hndg : (Polynomial.map φ g').natDegree = g'.natDegree :=
      (congr_arg Polynomial.natDegree hg').trans (Polynomial.natDegree_eq_natDegree eg).symm
    rw [← hg', ← hh', Polynomial.resultant_map_map,
      ← norm_adjoinRoot_map φ h' g' hh'm, hndh, hndg]
    exact congrArg φ (IH h' g' hh'm)

#print axioms norm_eq_resultant_monic

/-- **Norm identity for elimination ideals** (Thesis Corollary 5.2).

For `h` monic of degree `m`, if a constant `P ∈ R` belongs to the ideal `⟨h, g⟩`
(i.e., `C(P) = h·a + g·b` for some `a, b`), then
`P^m = Res(h,g) · N(b̄)` where `N` is the algebra norm on `R[z]/(h)`.

This replaces the false claim that `Res(h,g) | P`. The `m`-th power relationship
suffices for the order additivity argument in the codim case of the lifting theorem. -/
theorem norm_identity_elim
    (R : Type*) [CommRing R]
    (h g : Polynomial R) (hm : h.Monic)
    (P : R) (hP_mem : Polynomial.C P ∈ Ideal.span ({h, g} : Set (Polynomial R))) :
    ∃ Q : R, P ^ h.natDegree = Polynomial.resultant h g * Q := by
  rw [Ideal.mem_span_pair] at hP_mem
  obtain ⟨a, b, hab⟩ := hP_mem
  have key : AdjoinRoot.mk h g * AdjoinRoot.mk h b = algebraMap R (AdjoinRoot h) P := by
    change _ = AdjoinRoot.mk h (Polynomial.C P)
    have := congr_arg (AdjoinRoot.mk h) hab
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, mul_comm] at this
    exact this
  have hnorm := congr_arg (Algebra.norm R) key
  rw [map_mul, norm_eq_resultant_monic R h g hm,
    Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasis' hm).basis] at hnorm
  simp only [Fintype.card_fin, AdjoinRoot.powerBasis'_dim] at hnorm
  exact ⟨Algebra.norm R (AdjoinRoot.mk h b), hnorm.symm⟩

/-! ### Complexification of real-analytic functions

Following Thesis §3.3.1: extend real-analytic functions from `ℝˢ` to holomorphic
functions on `ℂˢ`, and transfer order-invariance.

The key results are:
1. `analyticAt_complexify`: a real-analytic function extends to a holomorphic function
2. `holomorphic_eq_zero_of_real_eq_zero`: identity theorem — holomorphic on `ℂˢ`,
   zero on `ℝˢ` implies zero everywhere
3. `complexify_order_eq`: orders match between real and complex
4. `complexify_order_invariant`: constant order on `ℝˢ` implies constant order on `ℂˢ`
-/

section Complexification

open scoped Topology
open Filter

/-- A ℂ-multilinear map on `Fin s → ℂ` that vanishes on all tuples of standard basis
vectors is zero. This generalizes `continuousMultilinearMap_eq_zero_iff_basis` to ℂ. -/
private lemma cml_eq_zero_of_basis_eq_zero {s k : ℕ}
    (g : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin s → ℂ) ℂ)
    (h : ∀ v : Fin k → Fin s, g (fun i => Pi.single (v i) 1) = 0) : g = 0 := by
  ext x
  simp only [ContinuousMultilinearMap.zero_apply]
  have hx : ∀ i : Fin k,
      x i = ∑ j : Fin s, (x i j) • (Pi.single j (1 : ℂ) : Fin s → ℂ) := by
    intro i; funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
               mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have heq : x = fun i => ∑ j : Fin s, (x i j) • (Pi.single j (1 : ℂ) : Fin s → ℂ) :=
    funext hx
  rw [heq, show (g fun i => ∑ j : Fin s, x i j • (Pi.single j (1 : ℂ) : Fin s → ℂ)) =
      ∑ v : Fin k → Fin s, g (fun i => x i (v i) • (Pi.single (v i) (1 : ℂ) : Fin s → ℂ)) from
    g.toMultilinearMap.map_sum (fun i j => x i j • (Pi.single j (1 : ℂ) : Fin s → ℂ))]
  apply Finset.sum_eq_zero
  intro v _
  rw [g.map_smul_univ]
  simp [h v]

/-- The real embedding `ι : ℝˢ → ℂˢ` as a continuous ℝ-linear map. -/
private noncomputable def realEmbedding (s : ℕ) :
    (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) :=
  ContinuousLinearMap.pi (fun j =>
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj j))

@[simp]
private lemma realEmbedding_apply {s : ℕ} (x : Fin s → ℝ) :
    realEmbedding s x = Complex.ofReal ∘ x := by
  ext j; simp [realEmbedding]

/-- Standard basis vectors are in the image of the real embedding. -/
private lemma realEmbedding_single {s : ℕ} (j : Fin s) :
    realEmbedding s (Pi.single j 1) = Pi.single j (1 : ℂ) := by
  ext i; simp [realEmbedding, Pi.single_apply, apply_ite]

/-- **Identity theorem on ℝˢ ⊂ ℂˢ** (Thesis §3.3.1).

If `g : ℂˢ → ℂ` is holomorphic at `z₀ = ofReal ∘ x₀` and vanishes on `ℝˢ` near `x₀`,
then `g` has infinite vanishing order at `z₀` (i.e., all iteratedFDeriv vanish).

The proof shows each `iteratedFDeriv ℂ k g z₀` is a ℂ-multilinear map that
vanishes on real basis inputs (via the chain rule for `g ∘ ι`), hence is zero. -/
private lemma order_eq_top_of_real_eq_zero {s : ℕ}
    (g : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hg : AnalyticAt ℂ g (Complex.ofReal ∘ x₀))
    (hgz : ∀ᶠ x in 𝓝 x₀, g (Complex.ofReal ∘ x) = 0) :
    order ℂ g (Complex.ofReal ∘ x₀) = ⊤ := by
  rw [order_eq_top_iff]
  intro k
  set z₀ := Complex.ofReal ∘ x₀
  let ι : (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) := realEmbedding s
  have hι_eq : ⇑ι = fun x => Complex.ofReal ∘ x := funext realEmbedding_apply
  have hι_x₀ : ι x₀ = z₀ := by rw [hι_eq]
  -- Step 1: g ∘ ι = 0 near x₀, so all ℝ-iterated derivatives vanish
  have hgι_zero : (g ∘ ⇑ι) =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hgz] with x hx
    simp only [Function.comp_apply, hι_eq, hx, Pi.zero_apply]
  have hgι_deriv : iteratedFDeriv ℝ k (g ∘ ⇑ι) x₀ = 0 := by
    have h := (hgι_zero.iteratedFDeriv ℝ k).self_of_nhds
    rw [h]
    rcases k with _ | k
    · ext m; simp [iteratedFDeriv_zero_apply]
    · exact congr_fun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k) (0 : ℂ)) x₀
  -- Step 2: Local chain rule via open ball where g is smooth
  obtain ⟨p, r, hp⟩ := hg
  set U := Metric.eball z₀ r with hU_def
  have hU_open : IsOpen U := Metric.isOpen_eball
  have hz₀U : z₀ ∈ U := Metric.mem_eball_self hp.r_pos
  have hg_smooth : ContDiffOn ℝ ⊤ g U :=
    hp.analyticOnNhd.contDiffOn_of_completeSpace |>.restrict_scalars ℝ
  have hιU_open : IsOpen (ι ⁻¹' U) := hU_open.preimage ι.continuous
  have hx₀_ιU : x₀ ∈ ι ⁻¹' U := show ι x₀ ∈ U from hι_x₀ ▸ hz₀U
  have hchain_within : iteratedFDerivWithin ℝ k (g ∘ ⇑ι) (ι ⁻¹' U) x₀ =
      (iteratedFDerivWithin ℝ k g U z₀).compContinuousLinearMap (fun _ => ι) :=
    ι.iteratedFDerivWithin_comp_right (hg_smooth.of_le le_top)
      hU_open.uniqueDiffOn hιU_open.uniqueDiffOn (hι_x₀ ▸ hz₀U) le_top
  rw [iteratedFDerivWithin_of_isOpen k hιU_open hx₀_ιU,
      iteratedFDerivWithin_of_isOpen k hU_open hz₀U] at hchain_within
  -- Step 3: Connect ℝ and ℂ derivatives via restrictScalars
  have hcd : ContDiffAt ℂ (↑k) g z₀ :=
    hp.hasFPowerSeriesAt.analyticAt.contDiffAt.of_le le_top
  have hrestr : (iteratedFDeriv ℂ k g z₀).restrictScalars ℝ = iteratedFDeriv ℝ k g z₀ :=
    ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) hcd
  -- Step 4: iteratedFDeriv ℂ k g z₀ vanishes on all real inputs
  have hvanish : ∀ w : Fin k → (Fin s → ℝ),
      (iteratedFDeriv ℂ k g z₀) (fun i => ι (w i)) = 0 := by
    intro w
    have h1 : ((iteratedFDeriv ℂ k g z₀).restrictScalars ℝ).compContinuousLinearMap
        (fun _ => ι) = 0 := by
      rw [hrestr, ← hchain_within]; exact hgι_deriv
    have h2 := DFunLike.congr_fun h1 w
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.coe_restrictScalars,
      ContinuousMultilinearMap.zero_apply] at h2
    exact h2
  -- Step 5: Basis argument — vanishing on basis vectors implies zero
  apply cml_eq_zero_of_basis_eq_zero
  intro v
  rw [show (fun i => Pi.single (v i) (1 : ℂ)) =
      (fun i => ι (Pi.single (v i) (1 : ℝ))) from
    funext fun i => (realEmbedding_single (v i)).symm]
  exact hvanish _

/-- Complexify a continuous multilinear map from `(Fin s → ℝ)^n → ℝ` to
`(Fin s → ℂ)^n → ℂ` by expanding in the standard basis. -/
private noncomputable def complexifyMultilinear {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin s → ℂ) ℂ :=
  ∑ σ : Fin n → Fin s,
    Complex.ofReal (T (fun j => Pi.single (σ j) 1)) •
    (ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (1 : ℂ)).compContinuousLinearMap
      (fun j => ContinuousLinearMap.proj (σ j))

private lemma complexifyMultilinear_apply {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ)
    (v : (i : Fin n) → Fin s → ℂ) :
    complexifyMultilinear T v =
      ∑ σ : Fin n → Fin s,
        Complex.ofReal (T (fun j => Pi.single (σ j) 1)) * ∏ j : Fin n, v j (σ j) := by
  unfold complexifyMultilinear
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_one, Algebra.id.smul_eq_mul]

private lemma complexifyMultilinear_real {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ)
    (x : (i : Fin n) → Fin s → ℝ) :
    complexifyMultilinear T (fun i => Complex.ofReal ∘ x i) =
      Complex.ofReal (T x) := by
  rw [complexifyMultilinear_apply]
  simp only [Function.comp_apply]
  simp_rw [← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  have hx : x = fun i => ∑ j : Fin s, x i j • (Pi.single j (1 : ℝ) : Fin s → ℝ) := by
    ext i k; simp [Pi.single_apply]
  conv_rhs => rw [hx, T.map_sum]
  simp_rw [T.map_smul_univ, smul_eq_mul]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

private lemma complexifyMultilinear_norm_le {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    ‖complexifyMultilinear T‖ ≤ (s : ℝ) ^ n * ‖T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v; rw [complexifyMultilinear_apply]
  have hterm : ∀ σ : Fin n → Fin s,
      ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1)) * ∏ j, v j (σ j)‖ ≤
      ‖T‖ * ∏ j, ‖v j‖ := by
    intro σ
    have h1 : ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1))‖ ≤ ‖T‖ := by
      rw [Complex.norm_real]
      exact (T.le_opNorm _).trans_eq (by simp [Pi.norm_single])
    have h2 : ‖∏ j : Fin n, v j (σ j)‖ ≤ ∏ j, ‖v j‖ :=
      (Finset.norm_prod_le Finset.univ (fun j => v j (σ j))).trans (Finset.prod_le_prod
        (fun j _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (v j) (σ j)))
    exact (norm_mul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
  calc ‖∑ σ : Fin n → Fin s, Complex.ofReal (T (fun j => Pi.single (σ j) 1)) *
          ∏ j, v j (σ j)‖
      ≤ ∑ σ : Fin n → Fin s, ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1)) *
          ∏ j, v j (σ j)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin n → Fin s, ‖T‖ * ∏ j, ‖v j‖ :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (s : ℝ) ^ n * ‖T‖ * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        simp only [Fintype.card_fin, Nat.cast_pow]; ring

/-- Complexified formal multilinear series. -/
private noncomputable def complexifyFMS {s : ℕ}
    (p : FormalMultilinearSeries ℝ (Fin s → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin s → ℂ) ℂ :=
  fun n => complexifyMultilinear (p n)

private lemma complexifyFMS_radius_pos {s : ℕ}
    (p : FormalMultilinearSeries ℝ (Fin s → ℝ) ℝ) (hp : 0 < p.radius) :
    0 < (complexifyFMS p).radius := by
  obtain ⟨r, hr_pos, hr_lt⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (ENNReal.natCast_ne_top s) (ne_of_gt hp)
  set R : NNReal := (s : NNReal) * r
  have hR_lt : (↑R : ENNReal) < p.radius := by
    show ↑((s : NNReal) * r) < p.radius; rwa [ENNReal.coe_mul, mul_comm]
  have hsumm := p.summable_norm_mul_pow hR_lt
  have hR_eq : (R : ℝ) = ↑s * ↑r := by
    simp only [R, NNReal.coe_mul, NNReal.coe_natCast]
  have hle : (↑r : ENNReal) ≤ (complexifyFMS p).radius :=
    (complexifyFMS p).le_radius_of_summable <|
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun n => by
          calc ‖complexifyFMS p n‖ * (↑r : ℝ) ^ n
              ≤ ((↑s : ℝ) ^ n * ‖p n‖) * (↑r : ℝ) ^ n := by
                gcongr; exact complexifyMultilinear_norm_le (p n)
            _ = ‖p n‖ * (R : ℝ) ^ n := by rw [hR_eq]; ring)
        hsumm
  exact lt_of_lt_of_le (by exact_mod_cast hr_pos) hle

/-- A real-analytic function at a point has a holomorphic (ℂ-analytic) extension
to `Fin s → ℂ` near the corresponding complex point, with matching vanishing order.

The extension is defined by the same convergent power series with complex variables
substituted (Thesis Theorem 2.1.2). The order equality follows from the
identity theorem on `ℝˢ ⊂ ℂˢ`. -/
private lemma complexifyMultilinear_eq_zero_iff {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    complexifyMultilinear T = 0 ↔ T = 0 := by
  constructor
  · intro h
    ext x
    have h1 := DFunLike.congr_fun h (fun i => Complex.ofReal ∘ x i)
    simp only [ContinuousMultilinearMap.zero_apply] at h1
    rw [complexifyMultilinear_real] at h1
    exact_mod_cast h1
  · intro h; subst h
    ext v; simp [complexifyMultilinear_apply]

theorem analyticAt_complexify {s : ℕ}
    (f : (Fin s → ℝ) → ℝ) (x₀ : Fin s → ℝ)
    (hf : AnalyticAt ℝ f x₀) :
    ∃ f_ℂ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ f_ℂ (Complex.ofReal ∘ x₀) ∧
      (∀ᶠ x in 𝓝 x₀, f_ℂ (Complex.ofReal ∘ x) = Complex.ofReal (f x)) ∧
      order ℂ f_ℂ (Complex.ofReal ∘ x₀) = order ℝ f x₀ := by
  obtain ⟨p, r, hball⟩ := hf
  set q := complexifyFMS p
  set z₀ := Complex.ofReal ∘ x₀
  have hq_rad : 0 < q.radius := complexifyFMS_radius_pos p hball.radius_pos
  have hq_ball : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall hq_rad
  set f_ℂ := fun z : Fin s → ℂ => q.sum (z - z₀)
  have hf_ℂ_ball : HasFPowerSeriesOnBall f_ℂ q z₀ q.radius := {
    r_le := le_rfl
    r_pos := hq_rad
    hasSum := fun {y} hy => by
      have h := hq_ball.hasSum hy
      rw [zero_add] at h
      change HasSum _ (q.sum ((z₀ + y) - z₀))
      rw [add_sub_cancel_left]
      exact h }
  -- Agreement on reals helper
  have hagree : ∀ᶠ x in 𝓝 x₀, f_ℂ (Complex.ofReal ∘ x) = Complex.ofReal (f x) := by
    filter_upwards [Metric.eball_mem_nhds x₀ (lt_min hball.r_pos hq_rad)] with x hx
    set y := x - x₀
    have hy_e : edist y 0 < min r q.radius := by
      show edist (x - x₀) 0 < _
      rw [edist_dist, dist_zero_right, ← dist_eq_norm, ← edist_dist]
      exact Metric.mem_eball.mp hx
    have hy_r : y ∈ Metric.eball (0 : Fin s → ℝ) r :=
      Metric.mem_eball.mpr (lt_of_lt_of_le hy_e (min_le_left _ _))
    have h_edist : edist (Complex.ofReal ∘ y : Fin s → ℂ) (0 : Fin s → ℂ) =
        edist y (0 : Fin s → ℝ) := by
      simp only [edist_pi_def, Function.comp_apply, Pi.zero_apply, ← Complex.ofReal_zero,
        Complex.isometry_ofReal.edist_eq]
    have hy_q : (Complex.ofReal ∘ y : Fin s → ℂ) ∈ Metric.eball (0 : Fin s → ℂ) q.radius :=
      Metric.mem_eball.mpr (h_edist ▸ lt_of_lt_of_le hy_e (min_le_right _ _))
    have h_cplx := hf_ℂ_ball.hasSum hy_q
    have h_rw : ∀ n, q n (fun _ => Complex.ofReal ∘ y) =
        Complex.ofReal (p n (fun _ => y)) := fun n =>
      complexifyMultilinear_real (p n) (fun _ => y)
    simp_rw [h_rw] at h_cplx
    have h_eq := h_cplx.unique (Complex.ofRealCLM.hasSum (hball.hasSum hy_r))
    rwa [show z₀ + Complex.ofReal ∘ y = Complex.ofReal ∘ x from by
           ext i; simp only [z₀, y, Pi.add_apply, Function.comp_apply, Pi.sub_apply]; push_cast; ring,
         show x₀ + y = x from by ext; simp [y]] at h_eq
  refine ⟨f_ℂ, ⟨q, q.radius, hf_ℂ_ball⟩, hagree, ?_⟩
  · -- Order equality: order ℂ f_ℂ z₀ = order ℝ f x₀
    let ι : (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) := realEmbedding s
    have hι_eq : ⇑ι = fun x => Complex.ofReal ∘ x := funext realEmbedding_apply
    have hι_x₀ : ι x₀ = z₀ := by rw [hι_eq]
    set U := Metric.eball z₀ q.radius with hU_def
    have hU_open : IsOpen U := Metric.isOpen_eball
    have hz₀U : z₀ ∈ U := Metric.mem_eball_self hq_rad
    have hf_ℂ_smooth : ContDiffOn ℝ ⊤ f_ℂ U :=
      hf_ℂ_ball.analyticOnNhd.contDiffOn_of_completeSpace |>.restrict_scalars ℝ
    have hιU_open : IsOpen (ι ⁻¹' U) := hU_open.preimage ι.continuous
    have hx₀_ιU : x₀ ∈ ι ⁻¹' U := show ι x₀ ∈ U from hι_x₀ ▸ hz₀U
    have hf_cd : ContDiffAt ℝ ⊤ f x₀ := hball.hasFPowerSeriesAt.analyticAt.contDiffAt
    -- Agreement as EventuallyEq for compositions
    have hfeq : (f_ℂ ∘ ⇑ι) =ᶠ[𝓝 x₀] (Complex.ofRealCLM ∘ f) := by
      filter_upwards [hagree] with x hx
      show f_ℂ (ι x) = Complex.ofRealCLM (f x)
      rw [show (ι x : Fin s → ℂ) = Complex.ofReal ∘ x from congr_fun hι_eq x]
      exact hx
    -- Helper: chain rule gives iteratedFDeriv ℝ n (f_ℂ ∘ ι) x₀ =
    --   ((iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ).compCLM(ι)
    have hchain_eq : ∀ n : ℕ, iteratedFDeriv ℝ n (f_ℂ ∘ ⇑ι) x₀ =
        ((iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ).compContinuousLinearMap
          (fun _ => ι) := by
      intro n
      have h1 : iteratedFDerivWithin ℝ n (f_ℂ ∘ ⇑ι) (ι ⁻¹' U) x₀ =
          (iteratedFDerivWithin ℝ n f_ℂ U z₀).compContinuousLinearMap (fun _ => ι) :=
        ι.iteratedFDerivWithin_comp_right (hf_ℂ_smooth.of_le le_top)
          hU_open.uniqueDiffOn hιU_open.uniqueDiffOn (hι_x₀ ▸ hz₀U) le_top
      rw [iteratedFDerivWithin_of_isOpen n hιU_open hx₀_ιU,
          iteratedFDerivWithin_of_isOpen n hU_open hz₀U] at h1
      have hcd : ContDiffAt ℂ (↑n) f_ℂ z₀ :=
        hf_ℂ_ball.hasFPowerSeriesAt.analyticAt.contDiffAt.of_le le_top
      have hrestr : (iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ =
          iteratedFDeriv ℝ n f_ℂ z₀ :=
        ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) hcd
      rw [h1, hrestr]
    -- Helper: chain rule left for ofRealCLM ∘ f
    have hleft_eq : ∀ n : ℕ, iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x₀ =
        Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x₀) :=
      fun n => Complex.ofRealCLM.iteratedFDeriv_comp_left (hf_cd.of_le le_top) le_top
    -- Key: for all n, iteratedFDeriv vanishes in sync
    suffices h_zero_iff : ∀ n : ℕ, iteratedFDeriv ℂ n f_ℂ z₀ = 0 ↔
        iteratedFDeriv ℝ n f x₀ = 0 by
      simp only [order]
      have h_ne : ∀ n : ℕ, iteratedFDeriv ℂ n f_ℂ z₀ ≠ 0 ↔
          iteratedFDeriv ℝ n f x₀ ≠ 0 := fun n => (h_zero_iff n).not
      by_cases hex : ∃ n, iteratedFDeriv ℝ n f x₀ ≠ 0
      · have hex_c := (exists_congr fun n => h_ne n).mpr hex
        rw [dif_pos hex_c, dif_pos hex]
        exact congr_arg _ (Nat.find_congr' (fun {n} => h_ne n))
      · have : ¬ ∃ n, iteratedFDeriv ℂ n f_ℂ z₀ ≠ 0 :=
          fun h => hex ((exists_congr fun n => h_ne n).mp h)
        rw [dif_neg this, dif_neg hex]
    intro n
    constructor
    · -- iteratedFDeriv ℂ n f_ℂ z₀ = 0 → iteratedFDeriv ℝ n f x₀ = 0
      intro hc
      have h_comp_zero : iteratedFDeriv ℝ n (f_ℂ ∘ ⇑ι) x₀ = 0 := by
        rw [hchain_eq n, hc]; ext; simp
      have h_feq_deriv := (hfeq.iteratedFDeriv ℝ n).self_of_nhds
      rw [h_comp_zero, hleft_eq] at h_feq_deriv
      ext v
      have hv := DFunLike.congr_fun h_feq_deriv.symm v
      simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousMultilinearMap.zero_apply] at hv
      exact Complex.ofReal_eq_zero.mp hv
    · -- iteratedFDeriv ℝ n f x₀ = 0 → iteratedFDeriv ℂ n f_ℂ z₀ = 0
      intro hr
      have h_left_zero : iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x₀ = 0 := by
        rw [hleft_eq, hr]; ext; simp
      have h_feq_deriv := (hfeq.iteratedFDeriv ℝ n).self_of_nhds
      rw [h_left_zero] at h_feq_deriv
      have h_vanish : ((iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ).compContinuousLinearMap
          (fun _ => ι) = 0 := by rw [← hchain_eq]; exact h_feq_deriv
      apply cml_eq_zero_of_basis_eq_zero
      intro v
      rw [show (fun i => Pi.single (v i) (1 : ℂ)) = (fun i => ι (Pi.single (v i) (1 : ℝ))) from
        funext fun i => (realEmbedding_single (v i)).symm]
      have h2 := DFunLike.congr_fun h_vanish (fun i => Pi.single (v i) (1 : ℝ))
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.coe_restrictScalars,
        ContinuousMultilinearMap.zero_apply] at h2
      exact h2

/-- **Order-invariance transfer** (Thesis §3.3.1, complexification step).

If `f : ℝˢ → ℝ` is real-analytic and has constant vanishing order `μ` on `ℝˢ` near `x₀`,
then its holomorphic extension `f_ℂ` has constant vanishing order `μ` on `ℂˢ` near `x₀`.

The proof first shows `order ≥ μ` everywhere (each `iteratedFDeriv` of order `< μ` is a
holomorphic function vanishing on `ℝˢ`, hence zero by the identity theorem), then uses
upper semi-continuity of order (`isOpen_order_le_inter`) and connectivity to get `order = μ`. -/
theorem complexify_order_invariant {s : ℕ}
    (f_ℂ : (Fin s → ℂ) → ℂ) (μ : ℕ)
    (hf_an : AnalyticOnNhd ℂ f_ℂ (Set.univ : Set (Fin s → ℂ)))
    (hf_ne : f_ℂ ≠ 0)
    (hf_real_oi : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ),
      order ℝ (fun y => f_ℂ (Complex.ofReal ∘ y)) x = ↑μ)
    (hf_order_zero : order ℂ f_ℂ (0 : Fin s → ℂ) = ↑μ) :
    ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), order ℂ f_ℂ z = ↑μ := by
  -- Step 1: order ≤ μ near 0 (upper semi-continuity)
  have h_le : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), order ℂ f_ℂ z ≤ ↑μ := by
    have h_open := isOpen_order_le_inter s Set.univ isOpen_univ f_ℂ hf_an ↑μ
    exact Filter.Eventually.mono (h_open.mem_nhds ⟨Set.mem_univ _, le_of_eq hf_order_zero⟩)
      fun z ⟨_, h⟩ => h
  -- Step 2: order ≥ μ near 0 (identity theorem on each derivative of order < μ)
  have h_ge : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), ↑μ ≤ order ℂ f_ℂ z := by
    let ι : (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) := realEmbedding s
    have hι_eq : ⇑ι = fun x => Complex.ofReal ∘ x := funext realEmbedding_apply
    have hι_zero : ι 0 = (0 : Fin s → ℂ) := by rw [hι_eq]; ext; simp
    have hf_cd : ContDiff ℝ ⊤ f_ℂ := (hf_an.contDiff (n := ⊤)).restrict_scalars ℝ
    have hf_cd_c : ContDiff ℂ ⊤ f_ℂ := hf_an.contDiff (n := ⊤)
    -- For each j < μ, iteratedFDeriv ℂ j f_ℂ z = 0 in a neighborhood of 0
    suffices h_deriv_vanish : ∀ j < μ, ∀ᶠ z in 𝓝 (0 : Fin s → ℂ),
        iteratedFDeriv ℂ j f_ℂ z = 0 by
      -- Finite intersection: all j < μ simultaneously
      rcases μ with _ | μ
      · filter_upwards with z; simp
      · have := (Finset.range (μ + 1)).eventually_all.mpr
          (fun j hj => h_deriv_vanish j (Finset.mem_range.mp hj))
        filter_upwards [this] with z hz
        -- All derivatives of order < μ+1 vanish, so order ≥ μ+1
        unfold order; split_ifs with hex
        · exact Nat.cast_le.mpr (Nat.le_of_not_lt fun hlt =>
            Nat.find_spec hex (hz _ (Finset.mem_range.mpr hlt)))
        · exact le_top
    intro j hj
    -- Step 2a: iteratedFDeriv ℂ j f_ℂ (ι x) = 0 for all x near 0 in ℝˢ
    have hreal_vanish : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ),
        iteratedFDeriv ℂ j f_ℂ (ι x) = 0 := by
      filter_upwards [hf_real_oi] with x hx
      -- order ℝ (f_ℂ ∘ ι) x = μ > j
      have hderiv_real : iteratedFDeriv ℝ j (f_ℂ ∘ ⇑ι) x = 0 :=
        iteratedFDeriv_eq_zero_of_lt_order (by
          show (↑j : ℕ∞) < order ℝ (f_ℂ ∘ ⇑ι) x
          convert (Nat.cast_lt (α := ℕ∞).mpr hj : (↑j : ℕ∞) < ↑μ) using 1)
      -- Chain rule + restrictScalars + basis argument (same as order_eq_top_of_real_eq_zero)
      have hchain : iteratedFDeriv ℝ j (f_ℂ ∘ ⇑ι) x =
          (iteratedFDeriv ℝ j f_ℂ (ι x)).compContinuousLinearMap (fun _ => ι) :=
        ContinuousLinearMap.iteratedFDeriv_comp_right ι hf_cd x le_top
      have hrestr : (iteratedFDeriv ℂ j f_ℂ (ι x)).restrictScalars ℝ =
          iteratedFDeriv ℝ j f_ℂ (ι x) :=
        ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
          (hf_cd_c.contDiffAt.of_le le_top)
      have h_comp_zero : ((iteratedFDeriv ℂ j f_ℂ (ι x)).restrictScalars ℝ).compContinuousLinearMap
          (fun _ => ι) = 0 := by rw [hrestr, ← hchain]; exact hderiv_real
      apply cml_eq_zero_of_basis_eq_zero
      intro v
      rw [show (fun i => Pi.single (v i) (1 : ℂ)) = (fun i => ι (Pi.single (v i) (1 : ℝ))) from
        funext fun i => (realEmbedding_single (v i)).symm]
      have h2 := DFunLike.congr_fun h_comp_zero (fun i => Pi.single (v i) (1 : ℝ))
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.coe_restrictScalars,
        ContinuousMultilinearMap.zero_apply] at h2
      exact h2
    -- Step 2b: For each basis tuple b, z ↦ (iteratedFDeriv ℂ j f_ℂ z)(e_b) is holomorphic,
    -- vanishes on ℝˢ near 0, hence vanishes on ℂˢ near 0 by the identity theorem
    have hbasis_zero : ∀ b : Fin j → Fin s,
        ∀ᶠ z in 𝓝 (0 : Fin s → ℂ),
          (iteratedFDeriv ℂ j f_ℂ z) (fun i => Pi.single (b i) (1 : ℂ)) = 0 := by
      intro b
      set g_b : (Fin s → ℂ) → ℂ :=
        fun z => (iteratedFDeriv ℂ j f_ℂ z) (fun i => Pi.single (b i) (1 : ℂ))
      have hg_an : AnalyticAt ℂ g_b (0 : Fin s → ℂ) := by
        have h1 : AnalyticAt ℂ (iteratedFDeriv ℂ j f_ℂ) (0 : Fin s → ℂ) :=
          hf_an.iteratedFDeriv j _ (Set.mem_univ _)
        exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => Fin s → ℂ) ℂ
          (fun i : Fin j => Pi.single (b i) (1 : ℂ))).analyticAt
          (iteratedFDeriv ℂ j f_ℂ 0)).comp h1
      have hg_real_zero : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ), g_b (Complex.ofReal ∘ x) = 0 := by
        filter_upwards [hreal_vanish] with x hx
        show (iteratedFDeriv ℂ j f_ℂ (ι x)) (fun i => Pi.single (b i) 1) = 0
        rw [hx, ContinuousMultilinearMap.zero_apply]
      have hord_top : order ℂ g_b (Complex.ofReal ∘ (0 : Fin s → ℝ)) = ⊤ :=
        order_eq_top_of_real_eq_zero g_b 0
          (by rwa [show Complex.ofReal ∘ (0 : Fin s → ℝ) = (0 : Fin s → ℂ) from by ext; simp])
          hg_real_zero
      rw [show Complex.ofReal ∘ (0 : Fin s → ℝ) = (0 : Fin s → ℂ) from by ext; simp] at hord_top
      exact (eventuallyEq_zero_of_order_eq_top g_b 0 hg_an hord_top).mono
        fun z hz => by exact hz
    -- Step 2c: Finite intersection over basis tuples + cml_eq_zero_of_basis_eq_zero
    have := Finset.univ.eventually_all.mpr (fun b _ => hbasis_zero b)
    filter_upwards [this] with z hz
    apply cml_eq_zero_of_basis_eq_zero
    intro v
    exact hz v (Finset.mem_univ _)
  filter_upwards [h_le, h_ge] with z hle hge
  exact le_antisymm hle hge

/-- **Schwarz reflection / real restriction** (decomposition step 6, now PROVED).

A function `ψ` holomorphic at a real point `realEmbedding s x₀` restricts to a real-analytic
function on `ℝˢ`: `x ↦ Re (ψ (ofReal ∘ x))` is real-analytic at `x₀`. When `ψ` is a holomorphic
root section taking real values on the real slice, this is exactly the real root function.

This is the real-analyticity half of recovering real root sections from holomorphic ones in the
complexification approach to the delineation axiom. Proof: `ψ` is ℂ-analytic hence ℝ-analytic
(`restrictScalars`); precompose with the ℝ-linear embedding and postcompose with `Re`, both
continuous-linear hence analytic. -/
theorem real_restriction_analytic {s : ℕ}
    (ψ : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hψ : AnalyticAt ℂ ψ (realEmbedding s x₀)) :
    AnalyticAt ℝ (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) x₀ := by
  have h1 : AnalyticAt ℝ ψ (realEmbedding s x₀) := hψ.restrictScalars
  have h2 : AnalyticAt ℝ (fun x => ψ (realEmbedding s x)) x₀ :=
    h1.comp ((realEmbedding s).analyticAt x₀)
  exact (Complex.reCLM.analyticAt _).comp h2

/-- **Complexification of a pseudopolynomial family** (decomposition, hypothesis side, PROVED).

A polynomial family `g : ℝᵐ → ℝ[t]` whose coefficients are analytic at `0` and whose degree is
bounded by `N` complexifies to a family `gℂ : ℂᵐ → ℂ[t]` with analytic coefficients, agreeing with
`g` on the reals coefficient-wise near `0`. Built by complexifying each coefficient via
`analyticAt_complexify` and reassembling. This is the family-level half of the hypothesis-side glue
for the complexification approach to the delineation axiom. -/
theorem complexify_pseudopoly {m : ℕ} (N : ℕ)
    (g : (Fin m → ℝ) → Polynomial ℝ)
    (hdeg : ∀ w, (g w).natDegree ≤ N)
    (hcoeff_an : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0) :
    ∃ gℂ : (Fin m → ℂ) → Polynomial ℂ,
      (∀ i, AnalyticAt ℂ (fun z => (gℂ z).coeff i) (Complex.ofReal ∘ (0 : Fin m → ℝ))) ∧
      (∀ i, ∀ᶠ w in 𝓝 (0 : Fin m → ℝ),
        (gℂ (Complex.ofReal ∘ w)).coeff i = Complex.ofReal ((g w).coeff i)) := by
  have hex : ∀ i, ∃ cℂ : (Fin m → ℂ) → ℂ,
      AnalyticAt ℂ cℂ (Complex.ofReal ∘ (0 : Fin m → ℝ)) ∧
      (∀ᶠ w in 𝓝 (0 : Fin m → ℝ), cℂ (Complex.ofReal ∘ w) = Complex.ofReal ((g w).coeff i)) :=
    fun i => by
      obtain ⟨cℂ, han, hagree, _⟩ := analyticAt_complexify (fun w => (g w).coeff i) 0 (hcoeff_an i)
      exact ⟨cℂ, han, hagree⟩
  choose cℂ hcℂ_an hcℂ_agree using hex
  -- The coefficient at `j` of the assembled `gℂ z` is `cℂ j z` when `j ≤ N`, else `0`.
  have hco : ∀ (z : Fin m → ℂ) (j : ℕ),
      (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (cℂ i z)).coeff j
        = if j ≤ N then cℂ j z else 0 := by
    intro z j
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (N + 1)) j (fun i => cℂ i z)]
    simp [Finset.mem_range, Nat.lt_succ_iff]
  refine ⟨fun z => ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (cℂ i z), ?_, ?_⟩
  · intro j
    refine (?_ : AnalyticAt ℂ (fun z => if j ≤ N then cℂ j z else 0)
        (Complex.ofReal ∘ (0 : Fin m → ℝ))).congr (.of_forall fun z => (hco z j).symm)
    by_cases hj : j ≤ N
    · simpa only [hj, if_true] using hcℂ_an j
    · simpa only [hj, if_false] using analyticAt_const
  · intro j
    filter_upwards [hcℂ_agree j] with w hw
    rw [hco (Complex.ofReal ∘ w) j]
    by_cases hj : j ≤ N
    · rw [if_pos hj, hw]
    · rw [if_neg hj, Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg w) (not_le.mp hj)), Complex.ofReal_zero]

end Complexification

open scoped Topology
open Filter

/-! ### Axioms for the analytic core (to be proved)

The single axiom `analytic_pseudopoly_delineable` below is the only non-standard
axiom on which the main theorem `mccallum_3_2_3_generalized` depends. We plan to
decompose it into the following smaller pieces, each of which is a well-known
classical theorem of complex analysis:

**Decomposition plan:**

1. **`weierstrass_preparation_complex`** (TODO axiom) — classical Weierstrass
   preparation theorem for holomorphic functions in several complex variables.
   A holomorphic `f` on `Δ × Δ(0, R)` with `f(0, ·)` having a zero of order
   exactly `m` at `0` factors as `f = u · h` where `u` is a unit and
   `h(z, w) = w^m + a₁(z) w^{m-1} + ... + a_m(z)` is a "Weierstrass polynomial"
   with `aᵢ(0) = 0`. **Status:** Mathlib has the algebraic version
   (`PowerSeries.exists_isWeierstrassFactorization`) for formal power series
   over complete local rings. Bridging to convergent power series is the gap.

2. **`zariski_root_sections_complex`** (TODO axiom) — Zariski's 1975 theorem.
   For a Weierstrass polynomial `h(z, w)` with `disc(h)` of constant nonzero
   vanishing order on a connected open set in `ℂˢ`, `h` has holomorphic root
   sections `ψᵢ : Δ → ℂ` with constant multiplicities. **Status:** not in
   Mathlib; classical reference is Zariski's "Studies in equisingularity I"
   (1965) or Tougeron, *Idéaux de fonctions différentiables*.

3. **`real_root_section_of_complex`** (theorem, provable) — Schwarz reflection.
   If `ψ : Δ → ℂ` is holomorphic, takes real values on `Δ ∩ ℝˢ`, then its
   restriction to `Δ ∩ ℝˢ` is real-analytic with real-valued power series.

4. **`analytic_pseudopoly_delineable`** (theorem, provable from 1–3) — the
   real-analytic delineation result currently stated as an axiom.

For now, we state the monolithic axiom below; the decomposition is documented
here as the path toward a fully-axiom-free proof.
-/

/-- **Weierstrass–Zariski delineation** (Thesis §§3.3.5–3.3.9), full-base form.

The analytic family `g` lives over the **full** straightened base `ℝˢ × ℝᵉ` (section
coordinates `y ∈ ℝˢ`, transverse coordinates `w ∈ ℝᵉ`). We require:
* constant positive degree **along the section** (`hg_deg`, `hg_pos`);
* an auxiliary `P ∈ ⟨g, g'⟩` whose **full-base** vanishing order at the origin is finite
  (`hP_ne`) and constant **along the section** (`hP_oi`).

The conclusion is delineability **over the section**: finitely many analytic root functions
`η : ℝˢ → ℝ` with constant multiplicities for `g (·, 0)`.

**Why the full base (vs. the section alone).** Over the section alone the controlling order
is `⊤` exactly in the multiple-section case (`S ⊆ {disc = 0}`): there `P` and `disc(g)`
vanish identically on the section. McCallum's order argument uses the **ambient** order, which
stays finite. The transfer lemma `order_comp_partialHomeomorph_symm` supplies this finite,
section-invariant order to this axiom (it equals the ambient `polyOrder P` along `S`). This is
what lets us drop the old `non_null` hypothesis: order-invariance of `P` (no non-vanishing) is
exactly Rule 4.1's `ord_inv(disc)`.

**Why P is needed at all:** without it the statement is FALSE — `g(w)(t) = t² - w₁` has
constant degree 2 but roots `±√w₁`, not analytic. `P ∈ ⟨g, g'⟩` of constant order forces
`disc(g)` to have constant order (norm identity `P^m = ±disc(h)·Q` + order additivity),
stabilizing the root structure.

The proof requires (eventual decomposition): complexification (`analyticAt_complexify`,
`complexify_order_invariant` — proved); Weierstrass preparation `g_ℂ = u · h` (monic `h`) —
NOT in Mathlib; norm identity on the monic `h` (`norm_identity_elim` — proved) feeding the
reverse-order bridge `order_invariant_factor_of_mul` (proved); Zariski's 1975 root sections —
NOT in Mathlib; Schwarz reflection to real-analytic. -/
axiom analytic_pseudopoly_delineable
    (s e : ℕ)
    (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hg_coeff_an : ∀ i : ℕ, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (hg_pos : 0 < (g 0).natDegree)
    (hg_deg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ)
    (hP_an : AnalyticAt ℝ P 0)
    (hP_ne : order ℝ P 0 ≠ ⊤)
    (hP_elim : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) ∈
        Ideal.span ({g w, Polynomial.derivative (g w)} : Set (Polynomial ℝ)))
    (hP_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0) :
    ∃ (V : Set (Fin s → ℝ)), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧
      ∃ (k : ℕ) (η : Fin k → (Fin s → ℝ) → ℝ) (mult : Fin k → ℕ),
        (∀ i, AnalyticOn ℝ (η i) V) ∧
        (∀ y ∈ V, ∀ i j : Fin k, i < j → η i y < η j y) ∧
        (∀ y ∈ V, ∀ α : ℝ, (g (y, 0)).IsRoot α ↔ ∃ i : Fin k, α = η i y) ∧
        (∀ i, 0 < mult i) ∧
        (∀ y ∈ V, ∀ i, (g (y, 0)).rootMultiplicity (η i y) = mult i)

/-- The full vanishing order at a delineable root equals the root multiplicity.

This is the key step requiring the factorization argument: if `θ` is an analytic root
function with constant multiplicity `m` on `S`, then `f(x, t) = (t - θ(x))^m · q(x, t)`
(as analytic functions) with `q(x, θ(x)) ≠ 0`. All mixed partial derivatives of
`toMvPoly f` of order `< m` vanish at `(θ(a), a)` because each such derivative, when
expanded via the Leibniz rule on the factored form, retains a factor of `(t - θ(x))`.
The `m`-th pure `t`-derivative is nonzero (from rootMultiplicity = m). -/
private theorem orderFull_eq_rootMultiplicity_at_delineable_root
    {n : ℕ} (f : PolyR n) (S : Set (Fin n → ℝ))
    (a : Fin n → ℝ) (ha : a ∈ S)
    (hne : specialize f a ≠ 0)
    (θ : (Fin n → ℝ) → ℝ) (hθ_an : AnalyticOn ℝ θ S)
    (hθ_root : ∀ b ∈ S, (specialize f b).IsRoot (θ b))
    (m_val : ℕ) (hm : ∀ b ∈ S, (specialize f b).rootMultiplicity (θ b) = m_val) :
    orderFull f a (θ a) = ↑m_val := by
  simp only [orderFull, if_neg hne, hm a ha]

/-- **Order-invariance from delineability** (Thesis §3.3.9).

If `f` is analytically delineable on a preconnected set `S`, then for any continuous
root function `θ`, the full vanishing order `orderFull f` is constant on the section
graph `SectionGraph θ S`.

The proof uses:
1. `θ` agrees with one of the delineable root functions `θ_i` on each connected component
   (by root ordering + continuity), hence globally on preconnected `S`
2. `f(x, t) = (t - θ_i(x))^{m_i} · q_i(x, t)` where `q_i(x, θ_i(x)) ≠ 0`
3. Coordinate change `u = t - θ_i(x)` is an analytic diffeomorphism; in new coordinates
   `f = u^{m_i} · R(u, x)` with `R(0, x) ≠ 0`, giving `orderFull = m_i` (constant)

Generalizes `order_invariant_section_of_mult_one` from multiplicity 1 to arbitrary multiplicity.
The multiplicity-1 case avoids step 2-3 because `orderFull = 1` follows directly from the
nonvanishing first `t`-derivative (see `orderFull_eq_one_of_simple_root`). -/
theorem order_invariant_of_delineable
    {n : ℕ} (f : PolyR n) (S : Set (Fin n → ℝ))
    (hS_conn : IsPreconnected S)
    (hdel : AnalyticDelineable f S)
    (θ : (Fin n → ℝ) → ℝ)
    (hθ_cont : ContinuousOn θ S)
    (hθ_root : IsRootFunction f θ S) :
    OrderInvariantFull f (SectionGraph θ S) := by
  obtain ⟨k, θ_del, m, hθ_an, hθ_ord, hθ_roots, hm_pos, hm_const⟩ := hdel
  -- Handle empty S (vacuous)
  by_cases hS_ne : S.Nonempty
  swap
  · intro p hp q hq
    simp only [SectionGraph, mem_setOf_eq] at hp
    exact absurd ⟨p.1, hp.1⟩ hS_ne
  obtain ⟨a₀, ha₀⟩ := hS_ne
  -- k > 0 since θ is a root function and S is nonempty
  have hk_pos : 0 < k := by
    by_contra h; push_neg at h
    interval_cases k
    exact ((hθ_roots a₀ ha₀ (θ a₀)).mp (hθ_root a₀ ha₀)).elim (fun i => i.elim0)
  -- specialize f a ≠ 0 for a ∈ S (multiplicity of zero polynomial is 0, contradicts 0 < m i)
  have hne : ∀ a ∈ S, specialize f a ≠ 0 := by
    intro a ha habs
    have h1 := hm_const a ha ⟨0, hk_pos⟩
    rw [habs, Polynomial.rootMultiplicity_zero] at h1
    linarith [hm_pos ⟨0, hk_pos⟩]
  -- Step 1: θ agrees with some θ_del(i₀) on all of S
  suffices h_agree : ∃ i₀ : Fin k, ∀ a ∈ S, θ a = θ_del i₀ a by
    -- Step 2: orderFull = m(i₀) on the section graph → OrderInvariantFull
    obtain ⟨i₀, hi₀⟩ := h_agree
    intro p hp q hq
    simp only [SectionGraph, mem_setOf_eq] at hp hq
    rw [hp.2, hi₀ p.1 hp.1, hq.2, hi₀ q.1 hq.1]
    exact (orderFull_eq_rootMultiplicity_at_delineable_root f S p.1 hp.1 (hne p.1 hp.1)
      (θ_del i₀) (hθ_an i₀) (fun b hb => (hθ_roots b hb (θ_del i₀ b)).mpr ⟨i₀, rfl⟩)
      (m i₀) (fun b hb => hm_const b hb i₀)).trans
      (orderFull_eq_rootMultiplicity_at_delineable_root f S q.1 hq.1 (hne q.1 hq.1)
      (θ_del i₀) (hθ_an i₀) (fun b hb => (hθ_roots b hb (θ_del i₀ b)).mpr ⟨i₀, rfl⟩)
      (m i₀) (fun b hb => hm_const b hb i₀)).symm
  -- Define the index function: for a ∈ S, j(a) is the unique i with θ(a) = θ_del(i)(a)
  have hj_exists : ∀ a ∈ S, ∃ i : Fin k, θ a = θ_del i a :=
    fun a ha => (hθ_roots a ha (θ a)).mp (hθ_root a ha)
  let j : (Fin n → ℝ) → Fin k := fun a =>
    if ha : a ∈ S then (hj_exists a ha).choose else ⟨0, hk_pos⟩
  have hj_spec : ∀ a (ha : a ∈ S), θ a = θ_del (j a) a := by
    intro a ha; simp only [j, dif_pos ha]; exact (hj_exists a ha).choose_spec
  -- j is ContinuousOn S: locally constant by root separation
  have hj_cont : ContinuousOn j S := by
    intro a₁ ha₁
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    -- θ a₁ = θ_del (j a₁) a₁, strictly separated from other root functions
    have hne_roots : ∀ l : Fin k, l ≠ j a₁ → θ a₁ ≠ θ_del l a₁ := by
      intro l hl; rw [hj_spec a₁ ha₁]
      rcases lt_or_gt_of_ne hl with h | h
      · exact ne_of_gt (hθ_ord a₁ ha₁ l (j a₁) h)
      · exact ne_of_lt (hθ_ord a₁ ha₁ (j a₁) l h)
    -- For each l ≠ j a₁, θ b ≠ θ_del l b eventually in 𝓝[S] a₁
    have hsep : ∀ l : Fin k, l ≠ j a₁ → ∀ᶠ b in 𝓝[S] a₁, θ b ≠ θ_del l b := by
      intro l hl
      exact ((hθ_cont a₁ ha₁).sub ((hθ_an l).continuousOn a₁ ha₁)).eventually
        (isOpen_ne.mem_nhds (sub_ne_zero.mpr (hne_roots l hl))) |>.mono
        fun b hb => sub_ne_zero.mp hb
    -- Finite conjunction: eventually ∀ l ≠ j a₁, θ b ≠ θ_del l b
    have h_all : ∀ᶠ b in 𝓝[S] a₁, ∀ l : Fin k, l ≠ j a₁ → θ b ≠ θ_del l b := by
      rw [Filter.eventually_all]
      intro l; by_cases hl : l = j a₁
      · exact Filter.Eventually.of_forall fun _ h => absurd hl h
      · exact (hsep l hl).mono fun _ hb _ => hb
    -- On S, separation forces j b = j a₁
    exact (h_all.and self_mem_nhdsWithin).mono fun b ⟨hb_sep, hb_S⟩ => by
      by_contra h_ne
      exact absurd (hj_spec b hb_S) (hb_sep (j b) h_ne)
  -- Apply IsPreconnected.constant
  have hj_const : ∀ a ∈ S, j a = j a₀ := fun a ha =>
    hS_conn.constant hj_cont ha ha₀
  exact ⟨j a₀, fun a ha => by rw [hj_spec a ha, hj_const a ha]⟩

/-! ### Local delineation via Weierstrass–Zariski -/

/-- **Local delineation** (Weierstrass–Zariski).

At each point `p ∈ S`, there exists a neighborhood `U` of `p` in `ℝⁿ` such that `f` is
analytically delineable on `S ∩ U` and order-invariant on each section graph.

The proof uses:
1. Submanifold chart (Theorem 2.2.1) to straighten `S` to a coordinate subspace,
2. `analytic_pseudopoly_delineable` to delineate the transformed family `g` on `ℝˢ`,
3. chart pullback to transfer root functions from `g` back to `f`,
4. `order_invariant_of_delineable` for order-invariance on section graphs. -/
theorem lifting_generalized_codim_local
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (p : Fin n → ℝ) (hp : p ∈ S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      AnalyticDelineable f (S ∩ U) ∧
      (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ (S ∩ U) → IsRootFunction f θ (S ∩ U) →
        OrderInvariantFull f (SectionGraph θ (S ∩ U))) := by
  -- Case split: if specialized degree is 0, delineation is trivial (no roots).
  by_cases h_deg_pos : 0 < (specialize f p).natDegree
  swap
  · -- Degree 0: specialize f a is a nonzero constant for all a ∈ S, hence has no roots
    have h_deg_zero : (specialize f p).natDegree = 0 := by omega
    have no_roots : ∀ a ∈ S, ∀ y : ℝ, ¬ (specialize f a).IsRoot y := by
      intro a ha y
      have hdeg_a : (specialize f a).natDegree = 0 := by rw [hdeg a ha p hp]; exact h_deg_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_a, Polynomial.IsRoot, Polynomial.eval_C]
      intro hc0
      exact hspec_ne a ha (by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_a, hc0, map_zero])
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_, ?_⟩
    · refine ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i,
        fun a ha y => ?_, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
      exact ⟨fun h => absurd h (no_roots a (Set.inter_univ S ▸ ha) y),
        fun ⟨i, _⟩ => Fin.elim0 i⟩
    · intro θ _ hθ_root
      exfalso
      exact no_roots p hp (θ p) (hθ_root p (Set.mem_inter hp (Set.mem_univ _)))
  -- Step 1: Apply the straightening chart (Theorem 2.2.1)
  obtain ⟨s, hs, Φ, hΦ_source, hΦ_val, hΦ_an_all, hΦ_symm_an, hΦ_straight⟩ :=
    hS_submfld.straightening_chart p hp
  have hΦ_an : AnalyticAt ℝ Φ p := hΦ_an_all p hΦ_source
  -- Step 2: Define the chart-to-submanifold map Ψ : ℝˢ → ℝⁿ
  -- Ψ(y) = Φ⁻¹(y, 0) embeds ℝˢ into S near p.
  let Ψ : (Fin s → ℝ) → (Fin n → ℝ) := fun y => Φ.symm (y, 0)
  have hΨ_zero : Ψ 0 = p := by
    show Φ.symm ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) = p
    rw [← hΦ_val]; exact Φ.left_inv hΦ_source
  have hΨ_an : AnalyticAt ℝ Ψ 0 := by
    let emb : (Fin s → ℝ) → (Fin s → ℝ) × (Fin (n - s) → ℝ) := fun y => (y, 0)
    have h_emb : AnalyticAt ℝ emb 0 := analyticAt_id.prod analyticAt_const
    have h_chart : AnalyticAt ℝ Φ.symm (emb 0) := by
      change AnalyticAt ℝ Φ.symm (0, 0); exact hΦ_val ▸ hΦ_symm_an
    exact h_chart.comp h_emb
  -- Step 3: Define the section family g(y) = specialize f (Ψ y) (used downstream)
  let g : (Fin s → ℝ) → Polynomial ℝ := fun y => specialize f (Ψ y)
  -- g(0) = specialize f p
  have hg_zero : g 0 = specialize f p := by show specialize f (Ψ 0) = _; rw [hΨ_zero]
  -- Step 4: Ψ maps into S for y near 0
  have hΦ_target_zero : ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) ∈ Φ.target := by
    rw [← hΦ_val]; exact Φ.map_source hΦ_source
  have hΨ_source : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target → Ψ y ∈ Φ.source :=
    fun y hy => Φ.map_target hy
  have hΨ_S : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target → Ψ y ∈ S := by
    intro y hy
    exact (hΦ_straight (Ψ y) (Φ.map_target hy)).mpr (by
      show (Φ (Φ.symm (y, (0 : Fin (n - s) → ℝ)))).2 = 0
      rw [Φ.right_inv hy])
  -- Step 5: Round-trip: for x ∈ S ∩ Φ.source, Ψ((Φ x).1) = x
  have hΨ_roundtrip : ∀ x ∈ S, x ∈ Φ.source → Ψ ((Φ x).1) = x := by
    intro x hxS hx_source
    have h2 : (Φ x).2 = 0 := (hΦ_straight x hx_source).mp hxS
    show Φ.symm ((Φ x).1, (0 : Fin (n - s) → ℝ)) = x
    conv_rhs => rw [← Φ.left_inv hx_source]
    congr 1
    exact Prod.ext rfl h2.symm
  -- Step 6: g(y) = specialize f x for x = Ψ y, so roots of g(y) = roots of f at x
  -- For x ∈ S ∩ Φ.source: specialize f x = g((Φ x).1)
  have hg_spec : ∀ x ∈ S, x ∈ Φ.source → specialize f x = g ((Φ x).1) := by
    intro x hxS hx_source
    show specialize f x = specialize f (Ψ ((Φ x).1))
    rw [hΨ_roundtrip x hxS hx_source]
  -- Step 7: g has constant degree d = f.natDegree for y near 0
  have hg_deg : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target →
      (g y).natDegree = (g 0).natDegree := by
    intro y hy
    show (specialize f (Ψ y)).natDegree = (specialize f (Ψ 0)).natDegree
    exact hdeg (Ψ y) (hΨ_S y hy) (Ψ 0) (hΨ_zero ▸ hp)
  -- Step 8: Build the full-base family `gfull` over `ℝˢ × ℝⁿ⁻ˢ` and the transferred `Pfull`.
  -- On the section, `gfull (y, 0) = g y` and `Pfull (y, 0) = P (Ψ y)` definitionally.
  let gfull : (Fin s → ℝ) × (Fin (n - s) → ℝ) → Polynomial ℝ :=
    fun w => specialize f (Φ.symm w)
  let Pfull : (Fin s → ℝ) × (Fin (n - s) → ℝ) → ℝ :=
    fun w => MvPolynomial.eval (Φ.symm w) P
  have hΦsymm_an0 : AnalyticAt ℝ Φ.symm (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)) := by
    show AnalyticAt ℝ Φ.symm ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ))
    exact hΦ_val ▸ hΦ_symm_an
  -- `eval · P` is globally smooth (it is a polynomial map)
  have hP_contdiff : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun a => MvPolynomial.eval a P) :=
    (show AnalyticOnNhd ℝ (fun a => MvPolynomial.eval a P) Set.univ from
      fun a _ => AnalyticOnNhd.eval_mvPolynomial P a (Set.mem_univ a)).contDiff
  -- Step 8a: `gfull` hypotheses (analytic coefficients; degree constant along the section)
  have hgfull_coeff_an : ∀ i : ℕ, AnalyticAt ℝ (fun w => (gfull w).coeff i) 0 := by
    intro i
    show AnalyticAt ℝ (fun w => (specialize f (Φ.symm w)).coeff i) 0
    simp only [specialize, Polynomial.coeff_map]
    exact (AnalyticOnNhd.eval_mvPolynomial (f.coeff i) (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hgfull_pos : 0 < (gfull 0).natDegree := by
    show 0 < (g 0).natDegree; exact hg_zero ▸ h_deg_pos
  have hgfull_deg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      (gfull (y, 0)).natDegree = (gfull 0).natDegree := by
    filter_upwards [(Φ.open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds
      hΦ_target_zero] with y hy
    exact hg_deg y hy
  -- Step 8b: `Pfull` hypotheses, with the (finite) order supplied by the chart transfer
  have hPfull_an : AnalyticAt ℝ Pfull 0 :=
    (AnalyticOnNhd.eval_mvPolynomial P (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hPfull_ne : order ℝ Pfull 0 ≠ ⊤ := by
    have htr : order ℝ Pfull 0 = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm 0) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) 0
        hΦ_target_zero hΦ_an_all hΦsymm_an0 hP_contdiff
    rw [htr]; exact polyOrder_ne_top_of_ne_zero P hP_ne (Φ.symm 0)
  have hPfull_elim : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)),
      Polynomial.C (Pfull w) ∈
        Ideal.span ({gfull w, Polynomial.derivative (gfull w)} : Set (Polynomial ℝ)) := by
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hP_mem
    filter_upwards with w
    apply Ideal.mem_span_pair.mpr
    let φ := MvPolynomial.eval (Φ.symm w)
    refine ⟨a.map φ, b.map φ, ?_⟩
    have hgw : gfull w = Polynomial.map φ f := rfl
    have h1 : a.map φ * gfull w + b.map φ * Polynomial.derivative (gfull w) =
        (a * f + b * Polynomial.derivative f).map φ := by
      rw [hgw, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          ← Polynomial.derivative_map]
    rw [h1, hab, Polynomial.map_C]
  have hPfull_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ Pfull (y, 0) = order ℝ Pfull 0 := by
    obtain ⟨W, hW_sub, hW_open, hxW⟩ := eventually_nhds_iff.mp hΦsymm_an0.eventually_analyticAt
    have hΦsymm_p : Φ.symm (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)) = p := hΨ_zero
    have hnbhd : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
        (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target ∩ W :=
      ((Φ.open_target.inter hW_open).preimage
        (continuous_id.prodMk continuous_const)).mem_nhds ⟨hΦ_target_zero, hxW⟩
    filter_upwards [hnbhd] with y hy
    have htr_y : order ℝ Pfull (y, 0)
        = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm (y, 0)) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) (y, 0)
        hy.1 hΦ_an_all (hW_sub _ hy.2) hP_contdiff
    have htr_0 : order ℝ Pfull 0
        = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm 0) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) 0
        hΦ_target_zero hΦ_an_all hΦsymm_an0 hP_contdiff
    rw [htr_y, htr_0]
    exact hP_oi (Φ.symm (y, 0)) (hΨ_S y hy.1) (Φ.symm 0) (by rw [hΦsymm_p]; exact hp)
  -- Step 9: Apply the delineation axiom to the full-base family
  obtain ⟨V, hV_open, hV_zero, k, η, mult, hη_an, hη_ord, hη_roots, hmult_pos, hmult_const⟩ :=
    analytic_pseudopoly_delineable s (n - s) gfull hgfull_coeff_an hgfull_pos hgfull_deg
      Pfull hPfull_an hPfull_ne hPfull_elim hPfull_oi
  -- Step 10: Shrink V to a connected neighborhood for preconnectedness.
  -- Intersect V with chart target projection, take connected component of 0.
  let Vt : Set (Fin s → ℝ) := V ∩ {y | (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target}
  have hVt_open : IsOpen Vt :=
    hV_open.inter (Φ.open_target.preimage (continuous_id.prodMk continuous_const))
  have hVt_zero : (0 : Fin s → ℝ) ∈ Vt := ⟨hV_zero, hΦ_target_zero⟩
  let V' : Set (Fin s → ℝ) := connectedComponentIn Vt 0
  have hV'_sub_Vt : V' ⊆ Vt := connectedComponentIn_subset Vt 0
  have hV'_sub_V : V' ⊆ V := fun y hy => (hV'_sub_Vt hy).1
  have hV'_target : ∀ y ∈ V', (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target :=
    fun y hy => (hV'_sub_Vt hy).2
  have hV'_open : IsOpen V' := hVt_open.connectedComponentIn
  have hV'_zero : (0 : Fin s → ℝ) ∈ V' := mem_connectedComponentIn hVt_zero
  have hV'_preconn : IsPreconnected V' := isPreconnected_connectedComponentIn
  -- Step 11: Define U = {x ∈ Φ.source | (Φ x).1 ∈ V'}
  let U : Set (Fin n → ℝ) := Φ.source ∩ (Prod.fst ∘ Φ) ⁻¹' V'
  have hU_open : IsOpen U :=
    Φ.continuousOn.fst.isOpen_inter_preimage Φ.open_source hV'_open
  have hU_p : p ∈ U := by
    refine ⟨hΦ_source, ?_⟩
    show (Φ p).1 ∈ V'
    have : (Φ p).1 = 0 := by
      have := congr_arg Prod.fst (show Φ p = (0, 0) from hΦ_val ▸ rfl)
      simp at this; exact this
    rw [this]; exact hV'_zero
  have hV'_in_V : ∀ a ∈ S ∩ U, (Φ a).1 ∈ V :=
    fun a ha => hV'_sub_V ha.2.2
  -- S ∩ U is preconnected: it equals Ψ '' V', continuous image of preconnected set
  have hSU_preconn : IsPreconnected (S ∩ U) := by
    have hΨ_image : Ψ '' V' ⊆ S ∩ U := by
      intro x ⟨y, hy, hxy⟩; subst hxy
      exact ⟨hΨ_S y (hV'_target y hy), hΨ_source y (hV'_target y hy), by
        show (Φ (Ψ y)).1 ∈ V'
        rw [show Φ (Ψ y) = (y, (0 : Fin (n - s) → ℝ)) from Φ.right_inv (hV'_target y hy)]
        exact hy⟩
    have hSU_sub_image : S ∩ U ⊆ Ψ '' V' := by
      intro a ⟨haS, ha_source, ha_V'⟩
      exact ⟨(Φ a).1, ha_V', hΨ_roundtrip a haS ha_source⟩
    rw [(hΨ_image.antisymm hSU_sub_image).symm]
    apply hV'_preconn.image Ψ
    intro y hy
    exact (Φ.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => hV'_target z hz)).continuousWithinAt (mem_of_mem_of_subset hy (subset_refl _))
  -- Extract delineability so both goals can use it
  have hdel : AnalyticDelineable f (S ∩ U) := by
    let θ' : Fin k → (Fin n → ℝ) → ℝ := fun i x => η i ((Φ x).1)
    refine ⟨k, θ', mult, ?_, ?_, ?_, hmult_pos, ?_⟩
    · intro i a ha
      have h_phi_fst : AnalyticAt ℝ (Prod.fst ∘ Φ) a :=
        analyticAt_fst.comp (hΦ_an_all a ha.2.1)
      have h_eta : AnalyticAt ℝ (η i) ((Prod.fst ∘ ↑Φ) a) :=
        (hη_an i).analyticAt (hV_open.mem_nhds (hV'_in_V a ha))
      exact (h_eta.comp h_phi_fst).analyticWithinAt
    · intro a ha i j hij
      exact hη_ord ((Φ a).1) (hV'_in_V a ha) i j hij
    · intro a ha y
      rw [hg_spec a ha.1 ha.2.1]
      exact hη_roots ((Φ a).1) (hV'_in_V a ha) y
    · intro a ha i
      rw [hg_spec a ha.1 ha.2.1]
      exact hmult_const ((Φ a).1) (hV'_in_V a ha) i
  refine ⟨U, hU_open, hU_p, hdel, ?_⟩
  -- Goal 2: Order-invariance on section graphs
  intro θ hθ_cont hθ_root
  exact order_invariant_of_delineable f (S ∩ U) hSU_preconn hdel θ hθ_cont hθ_root

/-! ### Globalization: local delineation on connected set → global -/

/-- Globalization of analytic delineability on a connected set (not necessarily open).
This generalizes `locally_delineable_to_global` from open sets to arbitrary connected sets.
The proof is a connectivity argument: root count and multiplicities are locally constant
in the subspace topology of `S`, hence constant on connected `S`. -/
theorem locally_delineable_to_global'
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (hdeg : DegreeInvariant f S)
    (_hnonzero : NotIdenticallyZeroOn f S)
    (hlocal : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)),
      IsOpen U ∧ a ∈ U ∧ AnalyticDelineable f (S ∩ U)) :
    AnalyticDelineable f S := by
  -- Step 1: Pick base point a₀ and get its local delineation
  obtain ⟨a₀, ha₀⟩ := hS_conn.nonempty
  obtain ⟨U₀, hU₀_open, ha₀U₀, k, θ₀, m₀, hθ₀_an, hθ₀_ord, hθ₀_roots, hm₀_pos, hm₀_const⟩ :=
    hlocal a₀ ha₀
  -- Step 2: Extract delineation data at each point
  have hlocal' : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (k' : ℕ)
      (θ' : Fin k' → (Fin n → ℝ) → ℝ) (m' : Fin k' → ℕ),
      IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOn ℝ (θ' i) (S ∩ U)) ∧
      (∀ b ∈ S ∩ U, ∀ i j : Fin k', i < j → θ' i b < θ' j b) ∧
      (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ' i b) ∧
      (∀ i, 0 < m' i) ∧
      (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ' i b) = m' i) := by
    intro a ha
    obtain ⟨U, hU, haU, k', θ', m', h1, h2, h3, h4, h5⟩ := hlocal a ha
    exact ⟨U, k', θ', m', hU, haU, h1, h2, h3, h4, h5⟩
  choose Uc kc θc mc hUc_open hUc_mem hθc_an hθc_ord hθc_roots _hmc_pos hmc_const using hlocal'
  -- Step 3: Root count is locally constant on S → constant by connectivity
  have hkc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ Uc a ha → kc a ha = kc b hb :=
    fun a b ha hb hab => strictMono_fin_card_eq _ _
      (hθc_ord a ha b hab) (hθc_ord b hb b ⟨hb, hUc_mem b hb⟩)
      (delineable_root_range_eq (S ∩ Uc a ha) (S ∩ Uc b hb) f
        (θc a ha) (θc b hb) (hθc_roots a ha) (hθc_roots b hb) b hab ⟨hb, hUc_mem b hb⟩)
  let rootCount : (Fin n → ℝ) → ℕ := fun a => if ha : a ∈ S then kc a ha else 0
  have hrc_cont : ContinuousOn rootCount S := by
    intro a ha
    rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
    exact Filter.mem_of_superset
      (inter_mem_nhdsWithin S ((hUc_open a ha).mem_nhds (hUc_mem a ha)))
      fun b ⟨hbS, hbU⟩ => show rootCount b = rootCount a by
        simp only [rootCount, dif_pos hbS, dif_pos ha]
        exact (hkc_agree a b ha hbS ⟨hbS, hbU⟩).symm
  have hkc_eq : ∀ a (ha : a ∈ S), kc a ha = k := by
    intro a ha
    have h1 := hS_conn.isPreconnected.constant hrc_cont ha ha₀
    simp only [rootCount, dif_pos ha, dif_pos ha₀] at h1
    have h2 : kc a₀ ha₀ = k := strictMono_fin_card_eq _ _
      (hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩)
      (hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩)
      (delineable_root_range_eq (S ∩ Uc a₀ ha₀) (S ∩ U₀) f
        (θc a₀ ha₀) θ₀ (hθc_roots a₀ ha₀) hθ₀_roots
        a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ ⟨ha₀, ha₀U₀⟩)
    omega
  -- Step 4: Multiplicities are locally constant → constant
  have hmc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ Uc a ha → ∀ i : Fin k,
      mc a ha (Fin.cast (hkc_eq a ha).symm i) = mc b hb (Fin.cast (hkc_eq b hb).symm i) := by
    intro a b ha hb hab i
    have hval_eq : θc a ha (Fin.cast (hkc_eq a ha).symm i) b =
        θc b hb (Fin.cast (hkc_eq b hb).symm i) b := by
      have hrange : Set.range (fun j : Fin k => θc a ha (Fin.cast (hkc_eq a ha).symm j) b) =
          Set.range (fun j : Fin k => θc b hb (Fin.cast (hkc_eq b hb).symm j) b) := by
        ext y; simp only [Set.mem_range]; constructor
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mp
            ((hθc_roots a ha b hab _).mpr ⟨_, rfl⟩)
          exact ⟨Fin.cast (hkc_eq b hb) j', hj'.symm⟩
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots a ha b hab _).mp
            ((hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mpr ⟨_, rfl⟩)
          exact ⟨Fin.cast (hkc_eq a ha) j', hj'.symm⟩
      exact congrFun (strictMono_fin_eq_of_range_eq _ _
        (fun p q hpq => hθc_ord a ha b hab _ _ (by exact_mod_cast hpq))
        (fun p q hpq => hθc_ord b hb b ⟨hb, hUc_mem b hb⟩ _ _ (by exact_mod_cast hpq))
        hrange) i
    have hm1 := hmc_const a ha b hab (Fin.cast (hkc_eq a ha).symm i)
    rw [hval_eq] at hm1
    exact hm1.symm.trans (hmc_const b hb b ⟨hb, hUc_mem b hb⟩ _)
  have hmc_eq : ∀ (a : Fin n → ℝ) (ha : a ∈ S) (i : Fin k),
      mc a ha (Fin.cast (hkc_eq a ha).symm i) = m₀ i := by
    intro a ha i
    let multFunc : (Fin n → ℝ) → ℕ := fun b =>
      if hb : b ∈ S then mc b hb (Fin.cast (hkc_eq b hb).symm i) else 0
    have hmc_cont : ContinuousOn multFunc S := by
      intro a' ha'
      rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
      exact Filter.mem_of_superset
        (inter_mem_nhdsWithin S ((hUc_open a' ha').mem_nhds (hUc_mem a' ha')))
        fun b ⟨hbS, hbU⟩ => show multFunc b = multFunc a' by
          simp only [multFunc, dif_pos hbS, dif_pos ha']
          exact (hmc_agree a' b ha' hbS ⟨hbS, hbU⟩ i).symm
    have h1 := hS_conn.isPreconnected.constant hmc_cont ha ha₀
    simp only [multFunc, dif_pos ha, dif_pos ha₀] at h1
    have hval₀ : θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm i) a₀ = θ₀ i a₀ := by
      have hrange₀ : Set.range (fun j : Fin k => θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm j) a₀) =
          Set.range (fun j => θ₀ j a₀) := by
        ext y; simp only [Set.mem_range]; constructor
        · rintro ⟨j, rfl⟩
          exact ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mp
            ((hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mpr ⟨_, rfl⟩)).imp
            fun _ h => h.symm
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mp
            ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mpr ⟨j, rfl⟩)
          exact ⟨Fin.cast (hkc_eq a₀ ha₀) j', hj'.symm⟩
      exact congrFun (strictMono_fin_eq_of_range_eq _ _
        (fun p q hpq => hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _ _ (by exact_mod_cast hpq))
        (fun p q hpq => hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩ p q hpq)
        hrange₀) i
    have hm₀ := hmc_const a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ (Fin.cast (hkc_eq a₀ ha₀).symm i)
    rw [hval₀] at hm₀
    have hm₀' := hm₀_const a₀ ⟨ha₀, ha₀U₀⟩ i
    omega
  -- Step 5: Construct k-indexed delineation at each point
  have hk_loc : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (θ : Fin k → (Fin n → ℝ) → ℝ),
      IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOn ℝ (θ i) (S ∩ U)) ∧
      (∀ b ∈ S ∩ U, ∀ i j : Fin k, i < j → θ i b < θ j b) ∧
      (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ i b) ∧
      (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ i b) = m₀ i) := by
    intro a ha
    refine ⟨Uc a ha, fun i => θc a ha (Fin.cast (hkc_eq a ha).symm i),
      hUc_open a ha, hUc_mem a ha, ?_, ?_, ?_, ?_⟩
    · exact fun i => hθc_an a ha _
    · intro b hb i j hij
      exact hθc_ord a ha b hb _ _ (by exact_mod_cast hij)
    · intro b hb y
      rw [hθc_roots a ha b hb y]
      exact ⟨fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha) i, hi⟩,
             fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha).symm i, by simpa using hi⟩⟩
    · intro b hb i
      exact (hmc_const a ha b hb (Fin.cast (hkc_eq a ha).symm i)).trans (hmc_eq a ha i)
  -- Step 6: Define global root functions and verify properties
  choose U_loc θ_loc h_all using hk_loc
  have hθ_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ U_loc a ha →
      (fun j => θ_loc a ha j b) = (fun j => θ_loc b hb j b) := by
    intro a b ha hb hab
    exact strictMono_fin_eq_of_range_eq _ _
      ((h_all a ha).2.2.2.1 b hab) ((h_all b hb).2.2.2.1 b ⟨hb, (h_all b hb).2.1⟩)
      (delineable_root_range_eq (S ∩ U_loc a ha) (S ∩ U_loc b hb) f
        (θ_loc a ha) (θ_loc b hb) (h_all a ha).2.2.2.2.1 (h_all b hb).2.2.2.2.1
        b hab ⟨hb, (h_all b hb).2.1⟩)
  refine ⟨k, fun i a => if ha : a ∈ S then θ_loc a ha i a else 0, m₀,
    ?_, ?_, ?_, hm₀_pos, ?_⟩
  · intro i
    apply analyticOn_of_locally_analyticOn
    intro a ha
    refine ⟨U_loc a ha, (h_all a ha).1, (h_all a ha).2.1, ?_⟩
    apply ((h_all a ha).2.2.1 i).congr
    intro b hb
    dsimp only
    rw [dif_pos hb.1]
    exact (congrFun (hθ_agree a b ha hb.1 hb) i).symm
  · intro a ha i j hij
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ i j hij
  · intro a ha y
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ y
  · intro a ha i
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.2 a ⟨ha, (h_all a ha).2.1⟩ i

/-- Globalization of order invariance on section graphs.
If `orderFull f · (θ ·)` is locally constant on a connected set `S`, it is globally
constant. -/
theorem order_invariant_of_locally_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (θ : (Fin n → ℝ) → ℝ)
    (hS_conn : IsConnected S)
    (_hθ_cont : ContinuousOn θ S)
    (_hθ_root : IsRootFunction f θ S)
    (hlocal : ∀ p ∈ S, ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      OrderInvariantFull f (SectionGraph θ (S ∩ U))) :
    OrderInvariantFull f (SectionGraph θ S) := by
  -- Extract local constancy of ordFun
  let ordFun := fun x => orderFull f x (θ x)
  have hlc : ∀ p ∈ S, ∃ U, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ S ∩ U, ordFun q = ordFun p := by
    intro p hp
    obtain ⟨U, hU, hpU, hOI⟩ := hlocal p hp
    exact ⟨U, hU, hpU, fun q ⟨hqS, hqU⟩ =>
      hOI ⟨q, θ q⟩ ⟨⟨hqS, hqU⟩, rfl⟩ ⟨p, θ p⟩ ⟨⟨hp, hpU⟩, rfl⟩⟩
  -- Unfold goal to ordFun a = ordFun b for a, b ∈ S
  intro ⟨a, _⟩ ha ⟨b, _⟩ hb
  simp only [SectionGraph, mem_setOf_eq] at ha hb
  obtain ⟨haS, rfl⟩ := ha; obtain ⟨hbS, rfl⟩ := hb
  show ordFun a = ordFun b
  -- Connectivity argument: ordFun is locally constant on S, hence constant
  choose Uloc hUloc_open hUloc_mem hUloc_const using hlc
  set c := ordFun a
  -- A covers {x ∈ S | ordFun x = c}, B covers the complement in S
  set A := ⋃ (x : {x // x ∈ S ∧ ordFun x = c}), Uloc x.1 x.2.1
  set B := ⋃ (x : {x // x ∈ S ∧ ordFun x ≠ c}), Uloc x.1 x.2.1
  have hA_open : IsOpen A := isOpen_iUnion fun x => hUloc_open x.1 x.2.1
  have hB_open : IsOpen B := isOpen_iUnion fun x => hUloc_open x.1 x.2.1
  have hS_sub : S ⊆ A ∪ B := by
    intro x hxS
    by_cases hxc : ordFun x = c
    · exact Or.inl (mem_iUnion.mpr ⟨⟨x, hxS, hxc⟩, hUloc_mem x hxS⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨x, hxS, hxc⟩, hUloc_mem x hxS⟩)
  have hSA : (S ∩ A).Nonempty :=
    ⟨a, haS, mem_iUnion.mpr ⟨⟨a, haS, rfl⟩, hUloc_mem a haS⟩⟩
  have hSAB_empty : ¬(S ∩ (A ∩ B)).Nonempty := by
    rintro ⟨x, hxS, hxA, hxB⟩
    obtain ⟨⟨y, hyS, hyc⟩, hxUy⟩ := mem_iUnion.mp hxA
    obtain ⟨⟨z, hzS, hzc⟩, hxUz⟩ := mem_iUnion.mp hxB
    have h1 : ordFun x = ordFun y := hUloc_const y hyS x ⟨hxS, hxUy⟩
    have h2 : ordFun x = ordFun z := hUloc_const z hzS x ⟨hxS, hxUz⟩
    exact hzc ((h2.symm.trans h1).trans hyc)
  -- By IsPreconnected, S ∩ B must be empty
  by_contra hne
  exact hSAB_empty (hS_conn.isPreconnected A B hA_open hB_open hS_sub hSA
    ⟨b, hbS, mem_iUnion.mpr ⟨⟨b, hbS, fun h => hne h.symm⟩, hUloc_mem b hbS⟩⟩)

/-! ### Case 1 ≤ s ≤ r - 2: S has positive codimension -/

/-- Case 1 ≤ s ≤ r - 2 of the generalized lifting theorem.
Proved from `lifting_generalized_codim_local` (local Weierstrass–Zariski axiom)
and globalization lemmas. -/
theorem lifting_generalized_codim_case
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (_hS_not_open : ¬ IsOpen S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  -- Step 1: Local delineation at each point (from the Weierstrass–Zariski axiom)
  have hlocal : ∀ p ∈ S, ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      AnalyticDelineable f (S ∩ U) ∧
      (∀ θ, ContinuousOn θ (S ∩ U) → IsRootFunction f θ (S ∩ U) →
        OrderInvariantFull f (SectionGraph θ (S ∩ U))) :=
    fun p hp => lifting_generalized_codim_local S f hS_submfld p hp
      hpos hsf hnonzero hdeg hspec_ne P hP_ne hP_mem hP_oi
  -- Step 2: Globalize analytic delineability
  refine ⟨locally_delineable_to_global' S f hS_conn hpos hdeg hnonzero
    (fun a ha => ?_), fun θ hθ_cont hθ_root => ?_⟩
  · obtain ⟨U, hU_open, haU, hU_del, _⟩ := hlocal a ha
    exact ⟨U, hU_open, haU, hU_del⟩
  -- Step 3: Globalize order invariance on section graphs
  · apply order_invariant_of_locally_invariant S f θ hS_conn hθ_cont hθ_root
    intro p hp
    obtain ⟨U, hU_open, hpU, _, hU_oi⟩ := hlocal p hp
    exact ⟨U, hU_open, hpU, hU_oi θ (hθ_cont.mono inter_subset_left)
      (fun a ha => hθ_root a ha.1)⟩

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
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
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
  · exact lifting_generalized_codim_case S f hS_submfld hS_conn hopen hpos hsf hnonzero hdeg hspec_ne P hP_ne hP_mem hP_oi

#print axioms lifting_theorem_generalized'

end
