import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.LaurentSeries

/-!
# Puiseux series (P1 of the Newton–Puiseux sub-project)

The field of **Puiseux series** over `K` is the field of Hahn series with *rational* exponents,
`PuiseuxSeries K := HahnSeries ℚ K`. Over a characteristic-zero algebraically closed field it is the
algebraic closure of the Laurent series field `K⸨X⸩ = HahnSeries ℤ K` (Puiseux's theorem, the target
of P3). This file sets up the basic objects:

* `PuiseuxSeries K` — the type, inheriting the `HahnSeries ℚ K` field structure;
* `PuiseuxSeries.monomial q r`, `PuiseuxSeries.X q` — Puiseux monomials `r·x^q`, `x^q`;
* `PuiseuxSeries.ofLaurent` — the embedding `K⸨X⸩ ↪ PuiseuxSeries K` (integer ⊆ rational exponents);
* `PuiseuxSeries.ramify m` — the ramification substitution `x = uᵐ` on exponents (`x^q ↦ u^{m·q}`),
  the key operation of the Newton–Puiseux algorithm, as a ring homomorphism.
-/

noncomputable section

open HahnSeries

/-- **Puiseux series** over `K`: Hahn series with rational exponents. -/
abbrev PuiseuxSeries (K : Type*) [Zero K] : Type _ := HahnSeries ℚ K

namespace PuiseuxSeries

variable {K : Type*}

/-- The Puiseux field structure is inherited from `HahnSeries ℚ K`. -/
example [Field K] : Field (PuiseuxSeries K) := inferInstance

/-- The Puiseux monomial `r · x ^ q` (`q : ℚ`). -/
def monomial [Zero K] (q : ℚ) (r : K) : PuiseuxSeries K := HahnSeries.single q r

/-- The Puiseux indeterminate raised to a rational power, `x ^ q`. -/
def X [Zero K] [One K] (q : ℚ) : PuiseuxSeries K := HahnSeries.single q 1

@[simp] theorem monomial_zero_right [Zero K] (q : ℚ) : monomial q (0 : K) = 0 :=
  map_zero (HahnSeries.single q)

/-- The order embedding `ℤ ↪o ℚ`, underlying `K⸨X⸩ ↪ PuiseuxSeries K`. -/
def ratOfIntEmb : ℤ ↪o ℚ where
  toFun := (Int.cast : ℤ → ℚ)
  inj' := Int.cast_injective
  map_rel_iff' := by simp

/-- The embedding of **Laurent series** into Puiseux series (integer exponents ⊆ rational), as a
ring homomorphism. -/
def ofLaurent [NonAssocSemiring K] : LaurentSeries K →+* PuiseuxSeries K :=
  embDomainRingHom (Int.castAddHom ℚ) Int.cast_injective (fun _ _ => by simp)

/-- **Ramification** `x = uᵐ`: the exponent-scaling substitution `x^q ↦ u^{m·q}`, as a ring
homomorphism `PuiseuxSeries K →+* PuiseuxSeries K`. This is the central operation of the
Newton–Puiseux algorithm (it turns a fractional-exponent series into an integer/finer-grid one). -/
def ramify [NonAssocSemiring K] (m : ℕ) (hm : 0 < m) :
    PuiseuxSeries K →+* PuiseuxSeries K :=
  embDomainRingHom (AddMonoidHom.mulLeft (m : ℚ))
    (by
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      simpa [AddMonoidHom.coe_mulLeft] using mul_right_injective₀ hm0)
    (fun g g' => by
      have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
      simp only [AddMonoidHom.coe_mulLeft]
      exact mul_le_mul_iff_right₀ hm0)

/-- Ramification scales exponents: `ramify m (r·x^q) = r·u^{m·q}`. -/
@[simp] theorem ramify_monomial [NonAssocSemiring K] (m : ℕ) (hm : 0 < m) (q : ℚ) (r : K) :
    ramify m hm (monomial q r) = monomial ((m : ℚ) * q) r := by
  show embDomainRingHom _ _ _ (single q r) = single _ r
  rw [embDomainRingHom_apply, embDomain_single]
  rfl

end PuiseuxSeries
