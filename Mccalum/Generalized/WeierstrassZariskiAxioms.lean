import Mccalum.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The two classical analytic axioms: convergent Weierstrass preparation & Zariski root sections

This file isolates the **two genuinely deep, classical analytic-geometry ingredients** of
McCallum's generalized lifting proof as clean, named axioms:

* `weierstrass_preparation_analytic` — convergent Weierstrass preparation (Phase C).
* `zariski_single_branch` — Zariski's Theorem 4.1.1: a single holomorphic root section
  (nonsplitting) under `disc ≢ 0` and constant discriminant order along the section (Phase E).

Both are stated at the **analytic-function level** (coefficients / roots as `AnalyticAt ℂ`
functions), deliberately decoupled from the germ-ring substrate `𝒪ₙ`
(`Mccalum.Generalized.AnalyticGerm`): the germ ring is an internal tool of Phase D and need not
appear in the public interfaces of C/E. The connective phases A, D, F (proved separately) wire the
real lifting axiom against these two, so that — once they are in place — the main theorem
`mccallum_3_2_3_generalized` depends only on these two axioms plus the standard
`propext, Classical.choice, Quot.sound`.

These are NOT the end state: both are standard, citable classical theorems (Weierstrass
preparation; Zariski equisingularity / Newton–Puiseux), to be discharged in a later effort. Stating
them crisply here pins down exactly the interface they must satisfy.

## Parameter conventions

The lifting problem has parameter space `ℝˢ × ℝᵉ` and a distinguished polynomial variable `t`.
Complexified, the parameter space is `CParam s e = (ℂˢ) × (ℂᵉ)`; the **section** is
`T = ℂˢ × {0}` (the `e`-directions are the "transverse" factor that only exists to make the
witness order finite — see the lifting axiom). Roots are localized at a real root `β` of
`g(0,0)`, shifted to `t = 0`, so a Weierstrass polynomial has all roots `→ 0` along `T`.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- Complexified parameter space: `s` section variables × `e` transverse variables. -/
abbrev CParam (s e : ℕ) : Type := (Fin s → ℂ) × (Fin e → ℂ)

/-- The monic degree-`m` polynomial `t^m + ∑_{i<m} a_i(w)·t^i` (a Weierstrass polynomial in `t`
when `a_i(0) = 0`), with coefficients evaluated at the parameter point `w`. -/
def weierstrassPoly {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (w : CParam s e) :
    Polynomial ℂ :=
  X ^ m + ∑ i : Fin m, C (a i w) * X ^ (i : ℕ)

/-- The discriminant of the section Weierstrass polynomial, as a function of the *full* parameter
`w` (its order along the section `T` is the Zariski equisingularity invariant). -/
def weierstrassDiscFn {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) :
    CParam s e → ℂ :=
  fun w => Polynomial.discr (weierstrassPoly m a w)

/-- **Convergent Weierstrass preparation (Phase C, AXIOM).**

If `G : (ℂˢ × ℂᵉ) × ℂ → ℂ` is analytic at the origin and its restriction `t ↦ G(0, t)` to the
distinguished line vanishes to order exactly `m > 0` at `t = 0`, then near the origin `G` factors
as a **unit** germ `u` (with `u(0) ≠ 0`) times a **monic Weierstrass polynomial** in `t` of degree
`m` whose coefficients `a_i` are analytic and vanish at the origin:

`G(w, t) = u(w, t) · (t^m + ∑_{i<m} a_i(w) · t^i)`  near `0`.

This is the classical convergent (analytic) Weierstrass preparation theorem. Mathlib has only the
*formal* version (`PowerSeries.exists_isWeierstrassFactorization`); the convergence of the factors
is the deep content. -/
axiom weierstrass_preparation_analytic {s e : ℕ}
    (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hm_pos : 0 < m)
    (hm : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ (u : CParam s e × ℂ → ℂ) (a : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      G =ᶠ[𝓝 0] fun wt => u wt * (weierstrassPoly m a wt.1).eval wt.2

/-- **Convergent Weierstrass division (Phase C, AXIOM) — existence.**

For a monic Weierstrass polynomial `h(z,t) = t^m + ∑ a_i(z) t^i` (coefficients analytic, `a_i(0)=0`)
and *any* germ `F` analytic at `0`, there exist an analytic quotient `q` and a degree-`< m`
**polynomial remainder** `r(z,t) = ∑_{i<m} ρ_i(z) t^i` (coefficients analytic) with

`F(z,t) = q(z,t) · h(z,t) + ∑_{i<m} ρ_i(z) t^i`  near `0`.

This is the analytic Weierstrass division theorem — the classical companion of
`weierstrass_preparation_analytic` (division follows from preparation). It is the interface needed
to push **germ-ring** Bézout cofactors down to **polynomial-in-`t`** cofactors over `𝒪ₙ[t]`, so that
`norm_identity_elim` (which lives in the polynomial ring) applies to the monic factor `h` — the
final step closing Phase D1. -/
axiom weierstrass_division_analytic {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (F : CParam s e × ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
      F =ᶠ[𝓝 0] fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)

/-- **Convergent Weierstrass division (Phase C, AXIOM) — uniqueness.**

The quotient/remainder of Weierstrass division are unique; equivalently, the only division of the
zero germ is the trivial one. This is the part used in the D1 descent: if a *polynomial-in-`t`* germ
is divisible by the monic `h` with an a-priori only-analytic quotient, that quotient is forced to be
polynomial (its non-polynomial part would be a nontrivial division of zero). -/
axiom weierstrass_division_unique {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ))
    (hq : AnalyticAt ℂ q 0) (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0)
    (hzero : (fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0

/-- **Zariski's theorem 4.1.1 — single holomorphic root section (Phase E, AXIOM).**

This is the *exact* statement of Theorem 4.1.1 of the thesis (an adaptation of Zariski 1975).
Given a monic Weierstrass polynomial `h(w, t) = t^m + ∑ a_i(w) t^i` (coefficients analytic,
`a_i(0) = 0`, so all roots cluster at `t = 0` on the section) whose **discriminant `F = disc(h)`
(i) does not vanish identically** (`order F 0 ≠ ⊤`) and **(ii) has constant vanishing order along the
section** `T = ℂˢ × {0}` near `0`, the roots of `h` over `T` are a **single** holomorphic section
`ψ : ℂˢ → ℂ` — the *unique distinct root* (nonsplitting) — of multiplicity `m`:

`h((y,0), α) = 0  ⟺  α = ψ(y)`  for `y, α` near `0`, with `rootMultiplicity (ψ y) = m`.

Both hypotheses match 4.1.1: `F ≢ 0` is "F does not vanish identically" (satisfied in the application
because `h` is squarefree, from squarefree `f`); constant order along `T` is the output of the
(ambient) order-additivity / `DiscOrder` step. The single-`ψ` conclusion is 4.1.1's nonsplitting; the
multiplicity `m` is its order-invariance of `h` along the graph of `ψ`. This is the single deepest
ingredient (Chapter 4 / Puiseux–Newton–monodromy); nothing of it is in Mathlib. -/
axiom zariski_single_branch {s e : ℕ}
    (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ ψ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m)

end
