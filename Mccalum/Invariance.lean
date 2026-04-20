import Mccalum.Basic
import Mccalum.Order

/-!
# Invariance conditions: degree-invariance, order-invariance, and non-vanishing

Definitions used to express hypotheses and conclusions of McCallum's theorems.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- `f` is **degree-invariant** on `S`. -/
def DegreeInvariant (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, (specialize f a).natDegree = (specialize f b).natDegree

/-- A base polynomial `g` is **order-invariant** on `S`. -/
def OrderInvariantMv (g : MvPolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder n g a = polyOrder n g b

/-- Order of `f ∈ ℝ[x₁,…,xₙ][xᵣ]` at `(a, y) ∈ ℝⁿ × ℝ`. -/
def orderFull (f : PolyR n) (a : Fin n → ℝ) (y : ℝ) : ℕ∞ :=
  polyOrder (n + 1) (toMvPoly f) (Fin.cons y a)

/-- A full polynomial `f` is **order-invariant** in `T ⊆ ℝⁿ × ℝ`. -/
def OrderInvariantFull (f : PolyR n) (T : Set ((Fin n → ℝ) × ℝ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, orderFull f p.1 p.2 = orderFull f q.1 q.2

/-- `f` is **not identically zero** on `S`. -/
def NotIdenticallyZeroOn (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ a ∈ S, specialize f a ≠ 0

end
