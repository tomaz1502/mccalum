# Scoping: proving `weierstrass_division` (axiom C) via the Cauchy-integral proof

Goal: discharge the single Phase-C axiom

```
weierstrass_division : (G analytic, G(0,·) of order m) →
   (∀ F analytic, ∃ q analytic, ρ : Fin m → coeffs analytic, F =ᶠ q·G + ∑ ρᵢ(z) tⁱ)  ∧  (uniqueness)
```

by the classical convergent proof (Hörmander §7.5 / Gunning–Rossi): construct `q` as a parametric
contour integral, `r = F − q·G`, and show `r` is a degree-`<m` polynomial in `t` with analytic
coefficients. We map every step to Mathlib (✅ have / 🟡 partial / ❌ gap).

---

## The classical construction

Fix `ε>0` with `G(0,·) ≠ 0` on `0 < |t| ≤ ε` (possible: `analyticOrderAt(G(0,·)) 0 = m` ⇒ `0` is an
*isolated* zero). By continuity + compactness, `G(z,·) ≠ 0` on `|t| = ε` for `z` near `0`. Then:

```
q(z,t) = (2πi)⁻¹ ∮_{|ζ|=ε}  F(z,ζ) / ( G(z,ζ) · (ζ − t) )  dζ        (|t| < ε)
r(z,t) = F(z,t) − q(z,t)·G(z,t)
```

Using the Cauchy formula `F(z,t) = (2πi)⁻¹∮ F(z,ζ)/(ζ−t) dζ`:

```
r(z,t) = (2πi)⁻¹ ∮  [F(z,ζ)/G(z,ζ)] · ( G(z,ζ) − G(z,t) )/(ζ − t)  dζ
```

The kernel `(G(z,ζ) − G(z,t))/(ζ − t)` is the **slope** `dslope` of `G(z,·)` (removable singularity
at `t=ζ`). The degree-`<m`-in-`t` of `r`, and the existence of exactly `m` zeros, are where the
order-`m` hypothesis enters — via the **argument principle**.

The cleanest internal factoring (and the one that isolates the hard input):

1. **Preparation** `G = u·W`, `W` monic of degree `m` in `t`, `u` a unit — via the contour
   power-sums `pₖ(z) = (2πi)⁻¹∮ ζᵏ G'(z,ζ)/G(z,ζ) dζ` and Newton's identities (`W = ∏(t−tⱼ(z))`).
   *Needs the zero count `= m`.*
2. **Division by `W`** (a genuine `t`-polynomial): `r = (2πi)⁻¹∮ (F/G)·[ (W(z,ζ)−W(z,t))/(ζ−t) ] dζ`;
   the bracket is a **polynomial in `t` of degree `m−1`** (finite difference of a monic degree-`m`
   polynomial), so `r = ∑_{k<m} ρₖ(z) tᵏ` with `ρₖ(z)` = contour integrals (analytic). *No count.*
3. **General division** = (2) composed with the unit `u` from (1): `q = q_W/u`, `r = r_W`.

---

## Mathlib inventory

### ✅ Have (strong)
- **Cauchy–Goursat / Cauchy integral formula**: `circleIntegral_eq_zero_of_differentiable_on_off_countable`,
  `DiffContOnCl.circleIntegral_eq_zero`, `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_…`,
  `DifferentiableOn.circleIntegral_sub_inv_smul` (`Analysis/Complex/CauchyIntegral.lean`).
- **`circleIntegral` / `circleMap`** with its API (`Analysis/Complex/Circle.lean`,
  `…/CauchyIntegral.lean`).
- **Removable singularity / slope**: `dslope`, `differentiableOn_dslope`,
  `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  (`Analysis/Complex/RemovableSingularity.lean`). Handles the difference-quotient kernel.
- **Parametric integral differentiation** over a field: `hasFDerivAt_integral_of_dominated_…`,
  `hasDerivAt_integral_of_dominated_…` (`Analysis/Calculus/ParametricIntegral.lean`,
  `…ParametricIntervalIntegral.lean`) — the engine for the keystone below.
- **`analyticOrderAt` factorization machinery** (project + Mathlib): gives `G(0,·) = tᵐ·v`, `v(0)≠0`.
- **`∮ dζ/(ζ−c) = 2πi`** on a circle (circleIntegral API) — base case of the argument principle.

### 🟡 Partial / must assemble
- **Keystone — holomorphy of a parametric contour integral.** No packaged
  "`z ↦ ∮ Φ(z,ζ) dζ` is `AnalyticAt`". Build from: `hasDerivAt_integral_of_dominated_…` over `ℂ`
  ⇒ `z` has a complex derivative (the contour is a fixed compact set; `Φ` jointly analytic, divisor
  non-zero on the contour gives the domination bound) ⇒ holomorphic ⇒ analytic. **Reusable workhorse**;
  every `q`, `ρₖ`, `pₖ` is analytic by this. *Moderate–hard.*
- **Difference-quotient = polynomial.** `(W(ζ)−W(t))/(ζ−t)` for `W` monic degree `m` in `t` is a
  degree-`m−1` polynomial in `t`: standard `Polynomial` finite-difference algebra (`Polynomial.sub`,
  geometric-sum identity `ζⁿ − tⁿ = (ζ−t)∑…`). *Easy–moderate.*

### ❌ Gap (the real obstruction)
- **Argument principle / zero count.** Mathlib has **no** argument principle, Rouché, or winding
  number (only Jensen's formula `MeromorphicOn.circleAverage_log_norm`, the averaged/log form). The
  needed statement:
  ```
  (2πi)⁻¹ ∮_{|ζ|=ε} G'(z,ζ)/G(z,ζ) dζ  =  (number of zeros of G(z,·) in |t|<ε, with multiplicity)
  ```
  - **Base case `z = 0` is already in reach** *without* the general principle: `G(0,·)'/G(0,·) =
    m/t + v'/v`; `∮ m/ζ = 2πi·m` (circle API) and `∮ v'/v = 0` (Cauchy–Goursat, `v≠0` on the disc).
    So `(2πi)⁻¹∮ G'(0,·)/G(0,·) = m`.
  - **Propagation to `z` near `0`:** the integral is analytic (keystone) hence continuous in `z`;
    if it is known to be `2πi·(an integer)` it is locally constant, hence `= m` near `0`. The missing
    fact is exactly "`(2πi)⁻¹∮ G'/G ∈ ℤ`" (logarithmic-derivative integral ∈ `2πiℤ`) — a special
    case of the argument principle. This is the one genuinely new analytic theorem to build (and a
    natural **upstream Mathlib contribution**).

---

## Dependency-ordered plan

| # | Step | Mathlib | Difficulty |
|---|------|---------|-----------|
| 1 | **Keystone**: `AnalyticAt ℂ (z ↦ (2πi)⁻¹∮_{|ζ|=ε} Φ(z,ζ) dζ) z₀` for jointly-analytic `Φ` with the contour in the analytic locus | build from ParametricIntegral + Cauchy | moderate–hard |
| 2 | Contour setup: `ε` with `G(0,·)≠0` on `0<\|t\|≤ε`; `G(z,·)≠0` on `\|t\|=ε` for `z` near `0` (continuity+compactness) | have | low–moderate |
| 3 | **Argument principle** `(2πi)⁻¹∮ G'/G = #zeros` (or just `∈ ℤ`), + base case `= m` at `z=0` | ❌ build / upstream | **hard (the gap)** |
| 4 | Power sums `pₖ(z)=(2πi)⁻¹∮ ζᵏG'/G` analytic (keystone) + Newton ⇒ **preparation** `G=u·W`, `deg_t W = m` | builds on 1,3 | hard |
| 5 | Difference-quotient `(W(ζ)−W(t))/(ζ−t)` = degree-`<m` `t`-polynomial | polynomial algebra | easy–moderate |
| 6 | **Division by `W`**: `r=∑_{k<m}ρₖ(z)tᵏ`, `ρₖ` analytic (keystone); `q` analytic | builds on 1,5 | moderate |
| 7 | **Assemble** general division `G=u·W` ⇒ `q=q_W/u`, `r=r_W`; **uniqueness** via the order argument (already used in `WeierstrassPrep`) | algebra | moderate |

**Critical path: 1 → 3.** Step 1 (keystone) is bounded and reusable; step 3 (argument principle) is
the genuine missing mathematics and the main risk/effort sink.

---

## Recommendations

- **First concrete step: build the keystone (step 1).** It is self-contained, reusable for every
  integral in the proof, and unblocks 4/6. Good standalone lemma to land and test.
- **Treat the argument principle (step 3) as a first-class sub-project**, ideally phrased for
  Mathlib upstream (`(2πi)⁻¹∮_{∂D} f'/f = ∑ orders of zeros − ∑ orders of poles`). Even the weaker
  "`∮ f'/f ∈ 2πiℤ`" suffices here (with the proved `z=0` base case + continuity).
- **Architecture note.** The Cauchy proof yields **preparation** most directly (step 4) and
  **division-by-`W`** cleanly (step 6); the repo currently has `weierstrass_division` as the axiom
  with `weierstrass_preparation_analytic` *derived* from it. Two clean options: (a) prove
  `weierstrass_division` using an internal Cauchy-preparation (the existing derived prep then becomes
  redundant but harmless); or (b) flip the primitive — make a `weierstrass_preparation` the axiom now,
  keep division derived, and discharge preparation by Cauchy. (b) matches the proof's natural shape.
- **Honest size.** C is bounded and standard but not small: ~1–2 months, dominated by step 3
  (argument principle) and step 1 (keystone). It remains *far* more self-contained than E (Zariski
  equisingularity / Puiseux–Newton–monodromy).
