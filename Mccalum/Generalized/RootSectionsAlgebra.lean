import Mccalum.Generalized.WeierstrassZariskiAxioms
import Mathlib.Algebra.Polynomial.Roots

/-!
# Phase F2 — root structure from the Zariski factorization

Zariski's `zariski_root_sections` produces a factorization of the section Weierstrass polynomial

`weierstrassPoly m a (y, 0) = ∏ᵢ (X − C (ψᵢ y))^{multᵢ}`.

This file extracts, by **pure polynomial algebra**, the per-root facts the final assembly (F3) needs:

* `isRoot_prod_X_sub_C_pow` — the roots of `∏ᵢ (X − C cᵢ)^{eᵢ}` (with `eᵢ > 0`) are exactly the `cᵢ`
  (exhaustiveness).
* `rootMultiplicity_prod_X_sub_C_pow` — when the `cᵢ` are pairwise distinct, the multiplicity of
  `cᵢ₀` is `eᵢ₀`.

Both are stated generically for `∏ᵢ (X − C cᵢ)^{eᵢ}` over `ℂ` and then specialized to
`weierstrassPoly` via the Zariski factorization equation.
-/

noncomputable section

open Polynomial

variable {r : ℕ} (c : Fin r → ℂ) (e : Fin r → ℕ)


/-- **F2 exhaustiveness.** The roots of `∏ᵢ (X − C cᵢ)^{eᵢ}` (with `eᵢ > 0`) are exactly the `cᵢ`. -/
lemma isRoot_prod_X_sub_C_pow (he : ∀ i, 0 < e i) (α : ℂ) :
    (∏ i : Fin r, (X - C (c i)) ^ (e i)).IsRoot α ↔ ∃ i, α = c i := by
  have key : ∀ i, (eval α ((X - C (c i)) ^ e i) = 0) ↔ α = c i := fun i => by
    rw [eval_pow, eval_sub, eval_X, eval_C, pow_eq_zero_iff (he i).ne', sub_eq_zero]
  rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, key]

/-- **F2 multiplicity.** If the `cᵢ` are pairwise distinct, the multiplicity of `cᵢ₀` in
`∏ᵢ (X − C cᵢ)^{eᵢ}` is exactly `eᵢ₀`. -/
lemma rootMultiplicity_prod_X_sub_C_pow (hc : Function.Injective c) (i₀ : Fin r) :
    (∏ i : Fin r, (X - C (c i)) ^ (e i)).rootMultiplicity (c i₀) = e i₀ := by
  rw [← Finset.prod_erase_mul Finset.univ (fun i => (X - C (c i)) ^ e i) (Finset.mem_univ i₀)]
  have herase_ne : (∏ i ∈ Finset.univ.erase i₀, (X - C (c i)) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero (c i))
  have hpow_ne : ((X - C (c i₀)) ^ e i₀) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero (c i₀))
  rw [rootMultiplicity_mul (mul_ne_zero herase_ne hpow_ne), rootMultiplicity_X_sub_C_pow]
  have hnotroot : ¬ (∏ i ∈ Finset.univ.erase i₀, (X - C (c i)) ^ e i).IsRoot (c i₀) := by
    rw [IsRoot, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [eval_pow, eval_sub, eval_X, eval_C]
    refine pow_ne_zero _ ?_
    rw [sub_ne_zero]
    intro heq
    exact (Finset.mem_erase.mp hi).1 (hc heq.symm)
  rw [rootMultiplicity_eq_zero hnotroot, zero_add]

/-! ## Specialization to the Zariski factorization of `weierstrassPoly` -/

variable {s e' : ℕ} {m : ℕ} {a : Fin m → (CParam s e' → ℂ)}
  {rr : ℕ} {ψ : Fin rr → ((Fin s → ℂ) → ℂ)} {mult : Fin rr → ℕ}

/-- Given the Zariski factorization at a fixed section point `y` (and `multᵢ > 0`), the roots of the
section polynomial are exactly the root sections `ψᵢ y`. -/
lemma weierstrass_section_isRoot
    (y : Fin s → ℂ)
    (hfac : weierstrassPoly m a ((y, 0) : CParam s e')
      = ∏ i : Fin rr, (X - C (ψ i y)) ^ (mult i))
    (hmult : ∀ i, 0 < mult i) (α : ℂ) :
    (weierstrassPoly m a ((y, 0) : CParam s e')).IsRoot α ↔ ∃ i, α = ψ i y := by
  rw [hfac]; exact isRoot_prod_X_sub_C_pow (fun i => ψ i y) mult hmult α

/-- Given the Zariski factorization at a section point `y` where the root sections take pairwise
distinct values, the multiplicity of `ψᵢ₀ y` in the section polynomial is `multᵢ₀`. -/
lemma weierstrass_section_rootMultiplicity
    (y : Fin s → ℂ)
    (hfac : weierstrassPoly m a ((y, 0) : CParam s e')
      = ∏ i : Fin rr, (X - C (ψ i y)) ^ (mult i))
    (hinj : Function.Injective (fun i => ψ i y)) (i₀ : Fin rr) :
    (weierstrassPoly m a ((y, 0) : CParam s e')).rootMultiplicity (ψ i₀ y) = mult i₀ := by
  rw [hfac]; exact rootMultiplicity_prod_X_sub_C_pow (fun i => ψ i y) mult hinj i₀

end
