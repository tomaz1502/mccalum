import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-! ## Analytic submanifold -/

variable {n : ℕ}

/-- `S` is an analytic `s`-dimensional submanifold of `ℝⁿ` (McCallum, Definition
p.20). For each `p ∈ S` there exist an open neighborhood `W` of `p` and an
analytic map `F : ℝⁿ → ℝ^{n-s}` for which `p` is a regular point (the Fréchet
derivative of `F` at `p` is surjective), such that `S ∩ W` is exactly the zero
set of `F` inside `W`. -/
def IsAnalyticSubmanifold (S : Set (Fin n → ℝ)) (s : Nat) : Prop :=
  S.Nonempty ∧
  s ≤ n ∧
    ∀ p ∈ S, ∃ W : Set (Fin n → ℝ), IsOpen W ∧ p ∈ W ∧
      ∃ F : (Fin n → ℝ) → (Fin (n - s) → ℝ),
        AnalyticOnNhd ℝ F W ∧
        Function.Surjective (fderiv ℝ F p) ∧
        (∀ x ∈ W, x ∈ S ↔ F x = 0)

@[simp]
def UnitSphere : Set (Fin 3 -> ℝ) := {x : Fin 3 → Real | x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1}

lemma UnitSphere_submanifold : IsAnalyticSubmanifold UnitSphere 2 := by
  constructor
  · unfold UnitSphere
    use fun x => (Real.sqrt 3) / 3
    grind
  · constructor
    · norm_num
    · intros p hp
      use Set.univ
      constructor
      · exact isOpen_univ
      · constructor
        · exact Set.mem_univ p
        · use fun x => by
            suffices Real by simp; use fun _ => this
            exact x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1
          simp
          constructor
          · admit
          · constructor
            · admit
            · intro x
              constructor
              · intro h
                rw [h]
                simp_all only [UnitSphere, Fin.isValue, Set.mem_setOf_eq, sub_self]
                rfl
              · intro h
                admit

#min_imports
