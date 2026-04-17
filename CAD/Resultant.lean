import Mathlib

open Polynomial MvPolynomial Matrix

variable {k : Type*} [Field k] {n : ℕ}

noncomputable abbrev φ (a : Fin n → k) : MvPolynomial (Fin n) k →+* k :=
  MvPolynomial.eval a

lemma resultant_map_eval (f g : Polynomial (MvPolynomial (Fin n) k))
    (a : Fin n → k) (m l : ℕ) :
    φ a (Polynomial.resultant f g m l) =
    Polynomial.resultant (f.map (φ a)) (g.map (φ a)) m l := by
  unfold Polynomial.resultant
  rw [RingHom.map_det, Polynomial.sylvester_map_map]

lemma resultant_eq_zero_of_common_root {p q : Polynomial k} {y : k}
    {m l : ℕ} (hm : p.natDegree ≤ m) (hl : q.natDegree ≤ l) (hml : m ≠ 0 ∨ l ≠ 0)
    (hp : p.eval y = 0) (hq : q.eval y = 0) :
    Polynomial.resultant p q m l = 0 := by
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant p q hm hl hml
  have heval : (p * a + q * b).eval y = (Polynomial.C (Polynomial.resultant p q m l)).eval y :=
    congrArg (Polynomial.eval y) hab
  simp [Polynomial.eval_add, Polynomial.eval_mul, hp, hq] at heval
  exact heval.symm

theorem no_common_root_of_resultant_ne_zero
    (f g : Polynomial (MvPolynomial (Fin n) k))
    (a : Fin n → k)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0)
    (h : φ a (Polynomial.resultant f g) ≠ 0) :
    ∀ y : k,
      ¬ ( Polynomial.eval y (f.map (φ a)) = 0
        ∧ Polynomial.eval y (g.map (φ a)) = 0) := by
  intro y ⟨hfy, hgy⟩
  rw [resultant_map_eval] at h
  exact h (resultant_eq_zero_of_common_root
    (Polynomial.natDegree_map_le)
    (Polynomial.natDegree_map_le)
    hdeg hfy hgy)
