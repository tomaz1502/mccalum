import Mccalum.Puiseux.OrderInvariance

/-!
# Conclusion 2, codim-1 — wiring spike

This file validates that the Newton–Puiseux parametrization (`exists_param_family`) composes with the
discriminant-bridge top theorem (`branchDiff_orders_eventually_constant_of_discNormalForm`).

`branch_orders_constant_e1` takes an irreducible, globalized Weierstrass family `q` over
`Fin (n+1) → ℂ` together with the discriminant `order` hypotheses *in exactly the hyperplane form
produced in `ZariskiE1.lean`* (`hconst`/`hord0`/`hHdisc_ne` there), and concludes Lemma 4.2.7 in its
consumable form: there is a parametrization `φ` and a primitive `m`-th root `ζ` whose
branch-difference orders are locally constant near the central section point `0`.

The remaining inputs taken as hypotheses here — `hsep_baseU` (separability on the parametrization
base), `hsep_nbhd` (separability off `u = 0` near the section), the contour radii `ρ < R`, and
`hdisc_vanish` (the discriminant vanishes on the hyperplane) — are exactly the obligations the full
`#21` wiring discharges from the disc normal form (`ZariskiE1.lean` already produces `hsep`,
`hord0`, `hconst`, and `hD0`).
-/

noncomputable section

open Polynomial Filter Topology Complex
open scoped Real

namespace Puiseux

/-- **Lemma 4.2.7 (codim-1, consumable form).** For an irreducible globalized Weierstrass family `q`
with the axiom's discriminant-order hypotheses, there exist a Puiseux parametrization `φ` and a
primitive `m`-th root of unity `ζ` such that `φ` parametrizes the roots of `q(cons(uᵐ, z))` and every
branch-difference order `ord_u(φ(z, ζⁱu) − φ(z, ζʲu))` is locally constant in the section variable
`z` near `0`. -/
theorem branch_orders_constant_e1 {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {δz c : ℝ} (hδz : 0 < δz)
    (hanaU : ∀ i, ∀ y ∈ baseU n δz c, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep_baseU : ∀ y ∈ baseU n δz c, (q y).Separable)
    (hsep_nbhd : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hdisc_vanish : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), y 0 = 0 → (q y).discr = 0)
    (hdisc_ne : order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ) ≠ ⊤)
    (hdisc_const : ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
        order ℂ (fun y => (q y).discr) w
          = order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ)) :
    ∃ (φ : (Fin n → ℂ) × ℂ → ℂ) (ζ : ℂ), IsPrimitiveRoot ζ m ∧
      (∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
        (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i j : Fin m, i ≠ j →
        analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
        = analyticOrderAt
            (fun u => φ ((0 : Fin n → ℂ), ζ ^ (i : ℕ) * u)
              - φ ((0 : Fin n → ℂ), ζ ^ (j : ℕ) * u)) 0) := by
  obtain ⟨φ, hroot, han, hiff⟩ :=
    exists_param_family q m hm hmonic hdeg hcont hana0 hq0 hirr hδz hanaU hsep_baseU
  have hζ : IsPrimitiveRoot (Complex.exp (2 * π * I / m)) m := Complex.isPrimitiveRoot_exp m hm.ne'
  refine ⟨φ, Complex.exp (2 * π * I / m), hζ, hroot, ?_⟩
  exact branchDiff_orders_eventually_constant_of_discNormalForm hm hmonic hdeg hcont hana0 hroot han
    hiff hζ (by simpa using hδz) hsep_nbhd hρ hρR hRc hdisc_vanish hdisc_ne hdisc_const

end Puiseux
