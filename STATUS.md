# Generalized McCallum Formalization — Status

## LAYER B COMPLETE — `weierstrass_division ⟸ {preparation, keystone}` (2026-06-01)
`weierstrass_division_via_cauchy` (`CDivisionByW.lean`, sorry-free, `#print axioms` = standard only):
the **entire** `weierstrass_division` axiom (existence **and uniqueness**) for a `t`-regular germ `G`
now follows, machine-checked, from just **two** inputs — a preparation `G = u·W` (Layer C) and the
**keystone** (= `osgood`, the SCV bridge) — both as hypotheses. The full Cauchy-integral proof of
Weierstrass division is done:
- **Existence**: `weierstrass_division_W_exists` (scalar Cauchy division `cauchy_division_scalar` +
  keystone for analyticity of `Q`, `ρ_k` + contour/domain extraction).
- **Uniqueness**: `weierstrass_division_W_unique` (Lagrange root bound → residue-at-infinity
  `circleIntegral_eq_zero_of_decay` via `rational_decay` → Cauchy recovery `cauchy_recovery_zero` →
  identity theorem `cauchy_uniqueness_scalar`; then `ρ_i =ᶠ 0` via `eq_zero_of_infinite_isRoot`).
  **Independent of the argument principle** (uses only elementary polynomial estimates + Mathlib's
  annulus Cauchy–Goursat + identity theorem).
- **Layer A** (`weierstrass_division_of_prep_div`) moves the unit `u`.

So the Cauchy proof of `C = weierstrass_division` is reduced to exactly **`{preparation (Layer C),
osgood}`**, with every other piece proved sorry-free. `mccallum_3_2_3_generalized` still rests on
`{weierstrass_division, zariski_single_branch}` (the discharge files are standalone WIP, not yet wired
into the main axiom path).

### `osgood` started — deployment scaffolding (`bridge_prod`)
Survey: Mathlib has the **torus integral** (`TorusIntegral.lean`) and the **1-variable** bridge
(`DifferentiableOn.analyticOnNhd`), but **no** several-variable bridge and **no** Hartogs/separately-
holomorphic. Key observation: the keystone needs the bridge for **joint** ℂ-differentiability (the
*easier* direction), deployed via `osgood` as the inductive core.

`bridge_prod` (`CBridge.lean`): the **inductive step**, formalized (compiles; its only `sorry` is
`osgood`). Given the bridge on `E'` (induction hypothesis) and `osgood`, it lifts the bridge to
`ℂ × E'`: jointly-differentiable ⟹ `z`-slices analytic (`bridge_one_var`) + `w`-slices analytic
(`E'`-bridge) + continuous ⟹ (`osgood`) jointly analytic. Iterating from `bridge_one_var` gives the
bridge on `ℂⁿ`.

**Polydisc–Cauchy route for the bridge (cleaner than `osgood` — avoids separate-analyticity).** Since
the keystone needs only the *joint*-differentiable ⇒ analytic direction, the bridge follows from the
polydisc Cauchy formula:
1–3. **`bridge_torus_repr` PROVED** (`CBridge.lean`, sorry-free, standard axioms): a jointly
   ℂ-differentiable `f : ℂ² → ℂ` equals, on a small polydisc, the **iterated double Cauchy integral**
   `f(z,w) = (2πi)⁻²∮_ζ∮_η f(ζ,η)/((ζ−z)(η−w))` — 1-var Cauchy in `z` on the holomorphic slice, then
   1-var Cauchy in `w` for each `ζ` on the `z`-circle, substituted under the outer integral.
   (`bridge_z_repr` is the standalone Step-1 version.)
4. **expand the kernel** `1/((ζ−z)(η−w)) = ∑_{j,k} …` and assemble a several-variable power series ⟹
   analytic.

**Step 4 = the SCV power-series construction — BUILD UNDERWAY** (`CSCVBridge.lean`, all sorry-free,
standard axioms). Plan: (1) Cauchy-kernel geometric expansion, (2) 2-var kernel product, (3)
term-by-term torus integration ⟹ `f = ∑_{j,k} c_{jk}(z−z₀)^j(w−w₀)^k`, (4) package `c_{jk}` into a
`FormalMultilinearSeries` (asymmetric `mkPiAlgebraFin` — avoids the binomial problem) ⟹
`HasFPowerSeriesOnBall`. Progress:
- **`hasSum_cauchy_kernel`** ✅ — `(ζ−z)⁻¹ = ∑_j (z−z₀)^j/(ζ−z₀)^{j+1}` for `‖z−z₀‖<‖ζ−z₀‖`.
- **`summable_norm_cauchy_kernel`** ✅ — the kernel series is absolutely summable (geometric).
- **`hasSum_cauchy_kernel_two`** ✅ — `(ζ−z)⁻¹·(η−w)⁻¹ = ∑_{(j,k)} (z−z₀)^j(w−w₀)^k/((ζ−z₀)^{j+1}(η−w₀)^{k+1})`
  over `ℕ×ℕ` (absolutely-convergent product of the two 1-var kernels, via `tsum_mul_tsum_of_summable_norm`).

- **`hasSum_z_expansion`** ✅ (Step 3, one variable): `2πi·f(z,w) = ∑_j ∮_ζ ((z−z₀)/(ζ−z₀))^j(ζ−z₀)⁻¹f(ζ,w)`
  for `‖z−z₀‖<r`. **Key discovery: the integral–sum swap is already in Mathlib** —
  `hasSum_two_pi_I_cauchyPowerSeries_integral` does the dominated convergence. This was the part I'd
  flagged as the hard analytic core of Step 3; it's free. So Step 3 is much more tractable than feared.

- **Step 4 algebraic core ✅** — `scvTerm`, `prod_range_ite`, **`scvTerm_apply_diag`**: the
  `FormalMultilinearSeries` on `ℂ²` built from coefficients `c : ℕ → ℕ → ℂ`, with diagonal evaluation
  `scvTerm c n (y,…,y) = ∑_{j+k=n} c_{jk}·y.1^j·y.2^{n-j}`. **The construction I feared (the binomial
  symmetrization) is avoided** by the asymmetric `mkPiAlgebraFin.compContinuousLinearMap` monomial
  (first `j` slots read coord 1, the rest coord 2 — diagonal value has no binomial). This is the heart
  of the packaging.

**Both scariest pieces are now done** (the integral–sum swap was free in Mathlib; the multilinear
construction went through asymmetrically).

**Assembly underway.** `hasSum_z_expansion'` ✅ — the clean `z`-expansion `2πi·f(z,w) = ∑_j (z−z₀)^j·B_j(w)`
with `B_j(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)` (coefficients pulled out of the integral). This is the form
that combines with the `w`-expansion. Remaining for the ℂ² bridge:
(a) expand each `B_j(w)` (analytic in `w` by the 1-var keystone) as `2πi·B_j(w) = ∑_k (w−w₀)^k·C_{jk}`,
and combine the iterated sums into the `ℕ×ℕ` HasSum `f = ∑_{j,k} c_{jk}(z−z₀)^j(w−w₀)^k` (needs the
`c_{jk}` Cauchy bound for summability of the double family) — *the remaining hard analysis: it needs
`B_j` differentiable in `w`, i.e. differentiate-under-integral*;
(b) **`hasSum_graded` ✅** — regroup the `ℕ×ℕ` monomial HasSum by total degree
(`HasSum.sigma` over `Finset.sigmaAntidiagonalEquivProd` + `sum_antidiagonal_eq_sum_range_succ`) to
match `scvTerm_apply_diag`. Pure HasSum algebra, done.
(c) radius/convergence ⟹ `HasFPowerSeriesOnBall` ⟹ `AnalyticAt`. Then the bridge follows from
`bridge_torus_repr`, and `osgood`/keystone via the `Fin n` induction (`bridge_prod`).

So the SCV build now has: Steps 1–3 ✅, Step 4 algebra (`scvTerm`, diagonal eval) ✅, clean
`z`-expansion ✅, graded reorg (b) ✅, **(a) differentiate-under-integral `Bj_hasDerivAt` ✅** — `B_j(w)`
is differentiable in `w` (via `circleIntegral_hasDerivAt`), given `f`, `∂_w f` jointly continuous on
`closedBall w₀ δ × sphere z₀ r` + the slice `HasDerivAt`.

**(c) diagonal HasSum `hasSum_scvTerm_diag` ✅** — from the `ℕ×ℕ` HasSum `∑_{j,k} c_{jk}y.1^jy.2^k = S`,
the series-of-homogeneous-parts `∑_n scvTerm c n (y,…,y) = S` (combines `scvTerm_apply_diag` +
`hasSum_graded`). This is the convergence half of `HasFPowerSeriesOnBall`.

So the SCV build now has, all sorry-free: Steps 1–3, Step 4 algebra (`scvTerm`, diagonal eval), clean
`z`-expansion, (a) `Bj_hasDerivAt`, (b) `hasSum_graded`, (c) `hasSum_scvTerm_diag`. **All three hard
cores + the diagonal/graded machinery are done.** Remaining for the ℂ² bridge:
- the `c_{jk}` Cauchy bound ⟹ the radius `R ≤ (scvSeries c).radius` (operator-norm estimate);
- assemble the `ℕ×ℕ` HasSum `f = ∑ c_{jk}…` from the `z`/`w` expansions (`Bj_hasDerivAt` ⟹ `B_j` analytic
  in `w`, needs `∂_w f` continuous via the Cauchy derivative estimate; then the double-sum combination);
- package `HasFPowerSeriesOnBall` (radius + `hasSum_scvTerm_diag`) ⟹ `AnalyticAt`; bridge from
  `bridge_torus_repr`. A continuing build of standard manipulations — no remaining hard core.

## Assembly spine started — Layer A PROVED (2026-06-01)
`CWeierstrassAssembly.lean` (standalone, not imported by `Mccalum.lean`) is the **assembly spine**
that derives the `weierstrass_division` axiom from its Cauchy-integral ingredients, each layer taking
the deeper one's output as an explicit hypothesis. Architecture:

```
weierstrass_division (division by a general t-regular germ G)
  ⟸ Layer A  { preparation: G = u·W ;  division by W (∃ + uniqueness) }   ← PROVED, sorry-free
  ⟸ Layer B  division by W   [keystone; Cauchy reproducing formula + difference-quotient brick]
  ⟸ Layer C  preparation G = u·W   [keystone + argument principle + Newton identities]
```

**Layer A — `weierstrass_division_of_prep_div` (sorry-free, `#print axioms` = standard only).** The
exact `weierstrass_division` conclusion (existence + uniqueness) follows from preparation `G = u·W`
(`u` an analytic unit, `u 0 ≠ 0`) + division-by-`W` by **pure analytic-germ algebra**: divide `F` by
`W` to get `F = Q·W + r`, set `q = Q·u⁻¹` (`u⁻¹` analytic since `u 0 ≠ 0`); then `q·G = Q·W`, so
`F = q·G + r` with the *same* degree-`<m` remainder `r`. Uniqueness transports via `q·G = (q·u)·W`.
No analysis beyond `AnalyticAt.mul`/`.inv` + `EventuallyEq`. This is the top of the tree: the axiom is
now machine-checked to follow from {preparation, division-by-W}.

**Layer B — first algebra brick PROVED.** `diffQuotient_eq_poly` (`CDivisionAlgebra.lean`,
sorry-free): the difference-quotient double sum `∑_j W_j ∑_{i<j} ζ^i t^{j-1-i}` reindexes to a genuine
degree-`<m` polynomial in `t`, `∑_{k<n} c_k(ζ)·t^k` with `c_k(ζ) = ∑_{k<j≤n} W_j·ζ^{j-1-k}`
(`n = natDegree W`). This is the form that makes the Cauchy remainder visibly `∑_{k<m} ρ_k(z)·t^k`
with `ρ_k(z) = (2πi)⁻¹∮ (F/W)·c_k dζ` (contour-integral coefficients). Proved by a `Finset.sum_bij'`
reindex `(j,i) ↦ (j-1-i, j)`.

**Layer B — scalar Cauchy division core PROVED.** `cauchy_division_scalar` (`CCauchyDivision.lean`,
sorry-free, `#print axioms` standard only): the genuine one-variable analytic heart. For a polynomial
`P` non-vanishing on `|ζ|=R` and `F` holomorphic on the closed disc,

  `F t = q·P(t) + ∑_{k<deg P} ρ_k·t^k`   for `|t|<R`,

with `q = (2πi)⁻¹∮ F/(P·(ζ−t))` and `ρ_k = (2πi)⁻¹∮ F·c_k/P` the explicit Cauchy contour integrals
(`c_k(ζ) = ∑_{k<j≤deg P} P_j ζ^{j-1-k}`). Proof = Mathlib's Cauchy reproducing formula
(`two_pi_I_inv_smul_circleIntegral_sub_inv_smul_…`) + the split `F/(ζ−t) = P(t)·F/(P(ζ)(ζ−t)) +
F·(P(ζ)−P(t))/(P(ζ)(ζ−t))`, with the second term turned into the explicit degree-`<m` polynomial via
`eval_sub_eval_eq_mul` + `diffQuotient_eq_poly`, then term-by-term integration. **No argument
principle.** This is the per-parameter statement.

**Layer B parametric packaging — first bricks PROVED** (`CDivisionByW.lean`, all sorry-free, standard
axioms):
- `weierstrassPoly_monic`, `weierstrassPoly_natDegree`: `W = X^m + ∑_{i<m} a_i X^i` is monic of degree
  exactly `m` (aligns the scalar lemma's `∑_{k<deg P}` with the target `∑ i : Fin m`).
- `weierstrassEval_analyticAt` (any point `(0,ζ₀)`), `weierstrassEval_continuous`,
  `weierstrassEval_zero` (`W(0,ζ) = ζ^m`).
- `qIntegrand_analyticAt`: the Cauchy **quotient** integrand `(z,t,ζ) ↦ F(z,ζ)/(W(z,ζ)·(ζ−t))` is
  jointly analytic at a contour point `((0,0),ζ₀)` (`ζ₀≠0`) — the keystone input for `Q`.
- `weierstrassPoly_coeff_analyticAt`: each `z ↦ W(z,·).coeff j` is analytic in `z`.
- `rhoIntegrand_analyticAt`: the Cauchy **remainder** integrand `(z,ζ) ↦ F(z,ζ)·c_k(z,ζ)/W(z,ζ)`
  (`c_k = ∑_{k<j≤m} W(z,·).coeff j·ζ^{j-1-k}`) is jointly analytic at `(0,ζ₀)` — the keystone input
  for the remainder coefficients `ρ_k`. **Both keystone inputs (`Q` and `ρ`) are now done.**

**Contour + domain extraction — PROVED** (`CDivisionByW.lean`, sorry-free, standard axioms):
- `weierstrass_contour`: for any `R > 0`, `W(z, ·) ≠ 0` on the circle `|ζ| = R` for all `z` near `0`
  (`W(0,ζ) = ζ^m ≠ 0`; tube lemma on the open "analytic-and-nonzero" set — run directly via joint
  analyticity at `(0,ζ)`, since the coefficients are only analytic at `0`, not globally continuous,
  so the Mathlib `exists_contour_ne_zero` brick — which needs global continuity — doesn't apply).
- `analyticAt_slice` / `exists_slice_analytic`: from `F` analytic at `0`, the slices `F(z,·)` are
  analytic on a common polydisc `‖z‖,‖ζ‖ < ρ` (⟹ the scalar lemma's `ContinuousOn`/`DifferentiableAt`
  hypotheses on any closed `ζ`-disc `R < ρ`).

**CAPSTONE (existence) PROVED — `weierstrass_division_W_exists`** (`CDivisionByW.lean`, sorry-free,
`#print axioms` standard only). Given the **keystone** as an explicit hypothesis (contour integrals
of jointly-analytic integrands are analytic in the parameter — exactly what `osgood` yields, stated
generically over a finite-dim complex normed space `H`), every analytic `F` divides as
`F =ᶠ[𝓝 0] Q·W + ∑_{i<m} ρ_i·t^i` with `Q`, `ρ_i` analytic — **exactly Layer A's `hdivW_exist`**.
Assembled from: `cauchy_division_scalar` applied per-`z` (slice domain from `exists_slice_analytic`,
contour from `weierstrass_contour`), `qIntegrand_analyticAt`/`rhoIntegrand_analyticAt` fed to the
keystone for analyticity of `Q`/`ρ_i`, and `weierstrassPoly_natDegree` + `Fin.sum_univ_eq_sum_range`
for `range m`↔`Fin m`. **This is the constructive heart of Layer B, done.**

**FULL CHAIN WIRED — `weierstrass_division_via_cauchy`** (`CDivisionByW.lean`, sorry-free, standard
axioms): the complete `weierstrass_division` conclusion (existence **and** uniqueness) for a
`t`-regular germ `G` now follows, machine-checked, from
`weierstrass_division ⟸ {preparation (G = u·W), keystone, uniqueness-of-division-by-W}`:
existence from the capstone, uniqueness threaded as a hypothesis, assembled through Layer A
(`weierstrass_division_of_prep_div`). The whole Cauchy-proof skeleton of `weierstrass_division` is
thus in place except for three named inputs: **preparation** (Layer C), **keystone** (= `osgood`), and
**uniqueness-of-division-by-W**.

**Uniqueness analysis (route found — does NOT need the argument principle).** `hdivW_uniq` reduces to:
for `z` near `0`, the remainder `r(z,·)` (degree `< m`) is `0`. Cleanest route discovered:
1. *Elementary root bound* — **PROVED**: `weierstrass_roots_eventually_in_ball` (`CDivisionByW.lean`,
   sorry-free, standard axioms). Every root `α` of `W(z,·)=t^m+∑a_i(z)t^i` satisfies
   `|α|^m ≤ ∑|a_i(z)||α|^i`; choosing `δ` with `δm < min(1, R^m)`, once `|a_i(z)| ≤ δ` the root is
   forced into `|α| < 1` then `|α|^m ≤ δm < R^m`. Hence **`∀ᶠ z, all roots of W(z,·) lie in `|ζ| < R`**
   — *no argument principle / no Mathlib continuity-of-roots needed*.
2. *Residue at infinity* — **PROVED**: `circleIntegral_eq_zero_of_decay` (`CCauchyDivision.lean`,
   sorry-free, standard axioms). If `g` is holomorphic on the closed exterior `{|z| ≥ R}` and decays
   `‖g z‖ ≤ C/‖z‖²` there, then `∮_{|z|=R} g = 0` — via Mathlib's **annulus** Cauchy–Goursat
   (`circleIntegral_eq_of_differentiable_on_annulus_off_countable`: `∮_R = ∮_{R'}`) plus the bound
   `‖∮_{R'}‖ ≤ 2πC/R' → 0`. Applied to the proper rational `r(ζ)/(W(ζ)(ζ−t))` (all poles inside, by
   the root bound), this forces the Cauchy quotient formula to *recover* `q`, so the zero germ gives
   `q ≡ 0`, `r ≡ 0`.
3. *Quotient recovery* — **PROVED**: `cauchy_recovery_zero` (`CCauchyDivision.lean`, sorry-free,
   standard axioms). If `Q·P + r = 0` on the circle `|ζ|=R` (`P ≠ 0` there) and the remainder integral
   `∮ r/(P(ζ−t)) = 0` (the residue input), then the Cauchy formula recovers `Q(t) = 0` for `|t| < R`
   (`Q(t) = (2πi)⁻¹∮ Q(ζ)/(ζ−t) = (2πi)⁻¹∮ −r(ζ)/(P(ζ)(ζ−t)) = 0`).

This makes uniqueness **independent of Layer C** — a separate, mostly-elementary effort. **All three
of its cores — root bound, residue at infinity, quotient recovery — are now machine-checked.**

**Per-parameter scalar uniqueness — PROVED**: `cauchy_uniqueness_scalar` (`CCauchyDivision.lean`,
sorry-free, standard axioms) combines the **identity theorem**
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`: `Q·P + r =ᶠ 0` near `0` ⟹ `= 0` on
the whole disc `ball 0 R'`, hence on the contour) with `cauchy_recovery_zero`: given `Q` holomorphic
on `ball 0 R'` (`R' > R`), `P ≠ 0` on `|ζ|=R`, `Q·P + r =ᶠ 0`, and the residue input `hres`, it
concludes `Q(t) = 0` for `|t| < R`.

**Decay bound — PROVED** (`CCauchyDivision.lean`, sorry-free, standard axioms):
- `norm_eval_le`: `‖p.eval ζ‖ ≤ (∑ⱼ‖p_j‖)·‖ζ‖^{deg p}` for `‖ζ‖ ≥ 1` (polynomial growth, upper).
- `rational_decay`: for `W` monic of degree `m ≥ 1` and `deg r < m`, `‖r(ζ)/(W(ζ)(ζ−t))‖ ≤ C/‖ζ‖²`
  for all `‖ζ‖ ≥ R₀` (`C = 4·A_r`). Uses the upper bound for `r`, the monic lower bound
  `‖W(ζ)‖ ≥ ‖ζ‖^m/2` (via `degree_sub_lt` on `W − X^m`), and `‖ζ−t‖ ≥ ‖ζ‖/2`. The residue lemma
  `circleIntegral_eq_zero_of_decay` was generalized to need decay only for *large* `‖ζ‖` (no
  compact-annulus argument). **This discharges the residue hypothesis `hres`.**

Remaining for `hdivW_uniq` — the **parametric assembly only**: apply `cauchy_uniqueness_scalar` at
each `z` near `0` (slice holomorphy from `Q` analytic at `0`; `W ≠ 0` outside from the root bound;
`hres` from `rational_decay` + `circleIntegral_eq_zero_of_decay`) to get `Q =ᶠ 0`, then `ρ_i =ᶠ 0`
from `H =ᶠ 0` (a degree-`<m` poly zero on a `t`-disc is `0`). All technical cores are now proved;
this is pure wiring.

Then Layer C (preparation, needs the argument principle) supplies the last hypothesis.
`#print axioms mccallum_3_2_3_generalized` unchanged.

## C discharge — Cauchy-integral proof scoped + first lemmas proved (2026-06-01)
Scoping doc: **`thesis/generalized/C_cauchy_scope.md`** (full plan, Mathlib inventory, dependency
order). Two genuinely-missing Mathlib ingredients identified as the critical path:
1. **Several-variable holomorphy ⇒ analyticity** (`DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U` for
   `U` open in `ℂⁿ`). Mathlib has this **only for one variable** (`DifferentiableOn.analyticAt`,
   `f : ℂ → E`). The `n`-variable lift is the keystone bottleneck — PR-sized, upstreamable.
2. **Argument principle** (`(2πi)⁻¹∮ G'/G = #zeros`). Mathlib has **none** (only Jensen's averaged
   form). Needed for the *propagation* `z=0 → z near 0`.

**Proved this session (sorry-free, WIP files, off the main axiom path):**
- `CKeystone.lean` — `circleIntegral_analyticAt_of_differentiable_nhds`: the keystone's analyticity
  step for **one** complex parameter (Mathlib's `DifferentiableOn.analyticAt` makes it free given
  differentiability on a nbhd). Documents the `n`-variable gap.
- `CArgPrinciple.lean` — the **argument-principle base case** `∮_{|ζ|=R} logDeriv(ζᵐ·v) dζ = 2πi·m`
  (`circleIntegral_logDeriv_pow_mul`), fully proved, via: `circleIntegral_const_div_center`
  (`∮ a/ζ = 2πi·a`, Cauchy formula) + `circleIntegral_logDeriv_eq_zero` (`∮ v'/v = 0`, Cauchy–Goursat)
  + `logDeriv_mul`/`logDeriv_pow` for the split. This is the `analyticOrderAt = m` ⟹ contour-integral
  connection, the heart of the argument-principle base case.

Remaining for C: the two gaps above (1 = keystone `n`-var bridge; 2 = argument-principle propagation),
then assembly (preparation via power sums + division-by-`W` via the polynomial difference quotient).
`#print axioms mccallum_3_2_3_generalized` unchanged = `{weierstrass_division, zariski_single_branch}`.

**Weierstrass-division bricks — all SCV-bridge-free pieces PROVED (sorry-free, wired in).** Toward
discharging `weierstrass_division` by the Cauchy-integral proof, every brick that does *not* require
the several-variable analyticity bridge is now proved:
- `CDivisionAlgebra.lean` — **difference-quotient factorization** `W(ζ)−W(t) = (ζ−t)·Q` with `Q` of
  `t`-degree `< deg W` (`eval_sub_eval_eq_mul`, `diffQuotient_tdeg_lt`). The remainder structure for
  division by a Weierstrass polynomial. Pure algebra.
- `CContour.lean` — **contour setup** (`exists_contour_ne_zero`): the multiplicity-`m` zero is
  isolated (finite order ⇒ isolated zeros), so `G(z₀,·) ≠ 0` on a circle `|t| = ε`, and (tube lemma)
  `G(z,·) ≠ 0` there for all `z` near `z₀`. The contour for the Cauchy quotient.
- `CArgPrinciple.lean` — argument-principle **base case** `∮ logDeriv(ζᵐ·v) = 2πi·m`.
- `CParamIntegral.lean` — the **one-parameter keystone** (below).

The single remaining obstruction for the whole Cauchy proof is the **several-variable
holomorphy⇒analyticity bridge** (`CBridge.osgood`): it gates the *multi-parameter* keystone (the
integrals depend on `z ∈ ℂⁿ`), which in turn gates the preparation (power sums) and division-by-`W`
assemblies. The 1-variable base case is proved; the `n`-variable lift is the multi-month SCV wall.

**Multi-parameter differentiate-under-integral — PROVED (`CParamIntegral.lean`, sorry-free).**
`circleIntegral_hasFDerivAt` / `circleIntegral_differentiableOn_multi`: for a parameter `z` in a
proper complex normed space `H` (e.g. `ℂⁿ` / `CParam`), `z ↦ ∮ Φ(z,ζ) dζ` is `DifferentiableOn ℂ` on
an open ball (Fréchet differentiate under the integral, via Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`). **This pins the entire remaining gap to *exactly*
the bridge**: the multi-parameter keystone is now `circleIntegral_differentiableOn_multi` (proved) +
`DifferentiableOn ℂ ⇒ AnalyticOnNhd ℂ` on `ℂⁿ` (`CBridge.osgood`, the one open lemma).

`circleIntegral_analyticAt_multi` (sorry-free) makes that reduction **machine-checked**: it takes the
bridge `DifferentiableOn ℂ ⇒ AnalyticOnNhd ℂ` on `H` as an explicit hypothesis and concludes the
multi-parameter keystone `AnalyticAt`. `#print axioms` = standard only (the bridge is a hypothesis,
not an axiom) — i.e. the multi-parameter keystone provably follows from the single bridge lemma.

*Note on axiom reduction:* turning `weierstrass_division` into a theorem (so the main theorem would
use the bridge instead) is **not** a reduction — the full Cauchy proof also needs the *argument
principle* (only its `z=0` base case is proved) plus the large power-sum/division assembly, so it
would trade one clean classical axiom for several deeper ones. The bricks are progress toward
*eliminating* `weierstrass_division` outright, not toward swapping it.

**One-parameter keystone — FULLY PROVED (`CParamIntegral.lean`, sorry-free, wired into the build).**
Three bricks of the Cauchy-integral proof of `weierstrass_division`:
- `circleIntegral_hasDerivAt` — **differentiate under a parametric circle integral** (via Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the domination is a constant bound on `Φ'` over
  the compact `closedBall z₀ δ × sphere c R`).
- `circleIntegral_differentiableOn` — differentiability on the open ball (pointwise at each interior
  point).
- `circleIntegral_analyticAt` — **the one-parameter keystone**: `z ↦ ∮ Φ(z,ζ) dζ` is `AnalyticAt` in
  `z ∈ ℂ`, given `Φ, Φ'` jointly continuous + the pointwise `z`-derivative (= what joint analyticity
  supplies). Closes via Mathlib's one-variable `DifferentiableOn.analyticAt`.
This is the **base case of the SCV recursion**, now verified. Remaining toward the keystone: the
*several*-parameter lift (the `n`-variable bridge below) and the analyticity-hypothesis extraction
(`uncurry Φ` analytic ⇒ `Φ,Φ'` jointly continuous — partial-derivative-of-analytic-is-analytic).

**`n`-variable bridge started — `CBridge.lean` (standalone WIP, has one `sorry`; deliberately NOT in
`Mccalum.lean` so the main library stays sorry-free).** Contents:
- `bridge_one_var` — the one-complex-variable base case, **proved** (it is Mathlib's
  `DifferentiableOn.analyticOnNhd`).
- `osgood` — the genuine several-complex-variables core, isolated with a `sorry` + precise proof
  outline (Hörmander Thm 2.2.8): Cauchy in `z` ⇒ `f = ∑ aₖ(w)(z−z₀)ᵏ` with `aₖ(w)` a contour integral
  of the `w`-analytic family `f(ζ,·)`; the `w`-analyticity of `aₖ` is the keystone in fewer variables,
  so the rigorous proof is a **simultaneous induction on `dim` of `{osgood, bridge, keystone}`**. This
  is the missing SCV development — a multi-week, upstream-Mathlib-sized contribution. The whole `ℂⁿ`
  bridge (and hence the keystone) reduces to `osgood` by induction on dimension (outline in-file).

## C collapsed to ONE axiom — base is now `{C, E}` = two axioms (2026-06-01)
**`#print axioms mccallum_3_2_3_generalized` = `{weierstrass_division, zariski_single_branch}` +
standard.** The whole generalized McCallum theorem rests on exactly **two** non-standard axioms, each a
verbatim classical theorem: **C = `weierstrass_division`** (convergent Weierstrass division by a
`t`-regular germ — existence + uniqueness, the Phase-C primitive) and **E = `zariski_single_branch`**
(Theorem 4.1.1). Full build green (2528 jobs).

The other Phase-C interfaces are now **theorems** derived from `weierstrass_division`:
- `weierstrass_division_analytic` / `_unique` — the special case `G = h` (in `WeierstrassZariskiAxioms.lean`);
- `weierstrass_preparation_analytic` — the corollary "divide `tᵐ` by `G`; the quotient is a unit"
  (`WeierstrassPrep.lean`). Proof = the *unit argument*: restrict to the line `w=0`, set
  `Ep = Xᵐ − ∑ρᵢ(0)Xⁱ`; from `Ep.eval =ᶠ q(0,·)·G(0,·)` and `analyticOrderAt(G(0,·)) = m` get
  `rootMult₀(Ep) = ord(q(0,·)) + m ≤ natDegree Ep = m`, forcing `ord(q(0,·)) = 0` (`q(0)≠0`, unit) and
  `rootMult₀(Ep) = m` (so `Xᵐ ∣ Ep`, hence `ρᵢ(0)=0`); then `u = q⁻¹`, `aᵢ = −ρᵢ`.

Both `{C, E}` are audited as faithful to the thesis (E ↔ Thm 4.1.1; C ↔ Thm 2.1.10 + classical
division). Remaining work to discharge them is the deep analysis: **C** via the Cauchy-integral
division formula (Mathlib has one-var Cauchy + parametric-integral derivative; only *formal* Weierstrass);
**E** = Zariski equisingularity / Chapter 4 (Puiseux–Newton–monodromy, none in Mathlib).

## Main theorem — `{C, E}` base REACHED, A2 ELIMINATED (2026-05-31)
`mccallum_3_2_3_generalized` (Projection.lean) — `#print axioms` = **exactly two classical inputs**:
`weierstrass_preparation_analytic` / `weierstrass_division_analytic` / `weierstrass_division_unique`
(C, Weierstrass preparation/division) and **`zariski_single_branch` (E)** + standard (`propext`,
`Classical.choice`, `Quot.sound`). **No sorries; full library builds (2527 jobs).** No real-analysis
axiom remains.

**`E = zariski_single_branch` now matches the thesis's Theorem 4.1.1 verbatim** (`thesis/thesis.pdf`):
a single holomorphic root section `ψ` (the *unique distinct root* — nonsplitting) of multiplicity `m`,
under hypotheses (i) `disc(h) ≢ 0` (`order F 0 ≠ ⊤`, "F does not vanish identically") and (ii)
`disc(h)` order-invariant along the section. The previous `zariski_root_sections` (general-`r`
factorization, and **missing** the `F ≢ 0` guard) did not match 4.1.1 and has been replaced.

**A2 is gone — no-splitting is part of Zariski 4.1.1, not a separate axiom.** History: the original
`real_delineation_of_complex_sections` (A2) was **unsound**; it was replaced by a sound stopgap
`real_cluster_single_branch` (A2′); then, after correcting the informal proof (see below) and matching
E to 4.1.1, A2′ was shown to be a *crutch* and **removed entirely** (`A2Axiom.lean` deleted). The
real-analytic content that survives is **proved, 0 custom axioms**: `real_delineation_of_single_branch`
(`A2Recovery.lean`) — single complex branch (real-valued on the slice via conjugation) ⟹ real-analytic
root delineation via Schwarz reflection.

**The chain** (`F3.lean` `single_cluster_real_delineation`): `cluster_from_real` (C + Zariski 4.1.1)
produces the single branch `ξ` + real-slice cover/multiplicity → `real_delineation_of_single_branch`
(proved). The complex chain collapsed to single-branch throughout
(`zariski_single_branch` → `cluster_root_structure` → `single_cluster_complex` →
`single_cluster_from_weierstrass` → `cluster_from_real`); the general-`r` machinery
(`weierstrass_section_isRoot`/`_rootMultiplicity` in `RootSectionsAlgebra.lean`) is now dead code
(builds, off the axiom path) — optional future deletion.

### Corrected informal proof (2026-05-31): `thesis/generalized/proof.tex`
Fixed a real defect in the generalized proof's key step (§5.4.4): the order-additivity lemma was
applied to `disc(h)` **restricted to the section** `T*`, which is `≡ 0` when `m ≥ 2` (e.g.
`f = x₃²−x₂` ⟹ `disc(h)=4x₂`, `≡0` on `{x₂=0}`). Corrected to use the **ambient** order along `T*`
(lemma `order_factor_const_of_mul_analytic` in `OrderMulAnalytic.lean` — audited, already the ambient
form; the Lean disc-order chain was ahead of the prose). Companion: `thesis/generalized/proof_corrected.md`.

The delineation is now a *theorem* (`analytic_pseudopoly_delineable'`, `Delineable.lean`): separable
case → analytic IFT; non-separable → `multi_cluster_real_delineation` (C+E+A2). The upper lifting chain
(`lifting_generalized_codim_local` → `…_codim_case` → `lifting_theorem_generalized'`) was relocated from
`Lifting.lean` to `Delineable.lean` (above the C/E/A2 stack) to break the import cycle, with the
dispatcher call fed the analytic Bézout cofactors (`Ideal.mem_span_pair` on `hP_mem`, `natDegree_map_le`
degree bounds). The remaining `{C, E, A2}` are the genuine classical inputs not in Mathlib.

## A2 PROOF EFFORT (2026-05-31) — recovery core PROVED; A2-as-stated found UNSOUND

**Proved (0 custom axioms):** `real_delineation_of_single_branch` (`A2Recovery.lean`). This is the
genuine real-analytic content of A2: given **one** holomorphic cluster section `ψ` parametrizing the
**unique** complex root of `(fam y).map(ℝ→ℂ)` in the cluster ball `δ₀` (real `y` near `0`) with constant
multiplicity `m`, the real root of `fam y` is a single real-analytic `η` with `η 0 = 0`, mult `m`.
Crux = conjugation: a real polynomial's complex roots are conjugate-closed, so the *unique* ball-root is
conj-fixed, hence real; Schwarz reflection (`real_root_function`, already proved) recovers `η = Re∘ψ∘ι`.
`#print axioms real_delineation_of_single_branch = [propext, Classical.choice, Quot.sound]`.

**Finding — `real_delineation_of_complex_sections` (A2) is UNSOUND as stated.** Its conclusion delivers
**one** root function `η`, but its hypotheses (general `r` complex branches, `hcover`, `hmult_match`,
`hsum`) are satisfied by genuinely-multi-real-root families. Concrete witness (`s=1`):
`fam_y(t) = (t − y₀)(t − 2y₀)` with `ψ₁(y)=y₀`, `ψ₂(y)=2y₀` (`r=2`, `mult=(1,1)`, `m=2`). Every A2
hypothesis holds, yet for `y₀>0` the family has **two** distinct real roots `y₀, 2y₀`, both `→0` — so no
single `η` satisfies the `(|α|<δ ∧ IsRoot α) ↔ α = η y` clause. ⇒ A2 ⊢ `False`. The current
`{C,E,A2}` base is therefore inconsistent (no exploit is wired, but it must be fixed).

**Root cause / residual.** The missing ingredient is **no-splitting**: under McCallum order-invariance a
multiplicity-`m` real root persists as a *single* branch of multiplicity `m` (does not split). That fact
needs the order-invariance witness `P` (`hP_ne`, `hP_oi_real`) — which A2's interface does **not** carry,
and which the counterexample violates (`disc = y₀²` drops order off the section). The `r=1` single-branch
case is exactly when A2 is true, and then it is fully provable (= the recovery core above). So A2's
content splits into: **(1) recovery — PROVED**, and **(2) no-splitting (`r=1`) — irreducible**, requiring
order-invariance / equisingularity not in Mathlib (Puiseux/Newton/monodromy absent). Cannot be derived
from `{C,E}` as stated.

**DONE (Option A implemented).** Replaced the unsound A2 with the sound `real_cluster_single_branch`
(A2′) carrying the order-invariance witness → single real branch `ξ`, then finished via the proved
recovery core. `F3.lean` rewired; full library green (2528 jobs); `#print axioms mccallum_3_2_3_generalized`
= `{C, E, real_cluster_single_branch} + standard`. Base is now **sound**; residual axiom = exactly the
no-splitting/equisingularity fact (not in Mathlib). See the milestone section at the top.

## ROADMAP: proving the axiom (Weierstrass → Zariski)
Full plan in **`WEIERSTRASS_ZARISKI_PLAN.md`** (6 phases A–F). Currently working **Phase A1**:
the *separable subcase* — if `disc(g(0,0)) ≠ 0` the section family has only simple roots, so the
axiom conclusion follows from the analytic IFT (no Weierstrass/Zariski), narrowing the axiom to the
`disc(g(0,0)) = 0` case.

### A1 sub-step DONE (2026-05-30): `analytic_root_section` (SimpleRoots.lean) — PROVED, 0 custom axioms
Generic **analytic implicit function theorem** for a scalar equation: `F : ℝⁿ×ℝ → ℝ` analytic at
`(y₀,t₀)`, `F(y₀,t₀)=0`, `∂ₜF(y₀,t₀) ≠ 0` ⟹ unique local analytic solution `t = φ(y)`. Extracted the
IFT machinery (analytic inverse function theorem on `G(y,t)=(y,F(y,t))`) away from polynomials, so
the **analytic family** `g(y,0)` (not just polynomial families `specialize f`) can use it.
`ift_local_root_section` is now its special case `F = (specialize f y).eval t` (refactor onto it
pending; currently both coexist).

### A1 sub-step DONE (2026-05-30): `fam_eval_analyticAt` (SimpleRoots.lean) — PROVED, 0 custom axioms
Joint analyticity of `(y,t) ↦ (fam y).eval t` for an analytic family `fam : ℝˢ → ℝ[t]` (analytic
coeffs, degree ≤ N near y₀). This is the `hF_an` input that `analytic_root_section` needs to run the
IFT at each simple root of the family. Proof: `(fam y).eval t = ∑_{i≤N} (fam y).coeff i · tⁱ` near
y₀ (degree bound), and the finite sum is jointly analytic.

### A1 COMPLETE (2026-05-30) — axiom narrowed to the multiple-root case
`analytic_pseudopoly_delineable` is now a **theorem** (Lifting.lean), proved by case-split on
`(g 0).Separable`:
- **separable** ⟹ `separable_family_locally_delineable` (SimpleRoots.lean) — the full analytic-family
  delineability for separable origin, PROVED (0 custom axioms): IFT at each simple root
  (`analytic_root_section` + `fam_eval_analyticAt` + `fam_eval_fderiv_t`), ordering by continuity,
  no-extra-roots via `Polynomial.cauchyBound` + tube lemma (`fam_eval_continuousOn`), exhaustiveness.
- **non-separable** ⟹ `analytic_pseudopoly_delineable_nonsep` (NEW narrowed axiom, hypothesis
  `¬ (g 0).Separable`).

`#print axioms mccallum_3_2_3_generalized` → `[analytic_pseudopoly_delineable_nonsep, propext,
Classical.choice, Quot.sound]`. Full build green, no sorries. The remaining axiom is now ONLY the
genuinely-deep `disc(g(0,0)) = 0` (multiple-root / equisingular) case — exactly the part needing
Weierstrass→Zariski (plan phases B–E). The easy case is off the trusted base.

New A1 lemmas (SimpleRoots.lean, all 0 custom axioms): `analytic_root_section` (generic analytic
IFT), `fam_eval_analyticAt`, `fam_eval_fderiv_t`, `fam_eval_continuousOn`,
`separable_family_locally_delineable`.

### D2 VALIDATED (2026-05-30): `disc_order_invariant_of_witness` (Lifting.lean) — 0 custom axioms
The algebraic spine of Phase D, assembled from **proven** lemmas: for a monic `h` (stub Weierstrass
output) with witness `P ∈ ⟨h, h'⟩` of constant order on connected `S`, `resultant(h, h')` (= disc up
to leading coeff) has constant order on `S`. Wiring = `norm_identity_elim` (`P^m = res·Q`, generic
`CommRing`) + reverse-order bridge `order_invariant_factor_of_mul`. Validated over `MvPolynomial`
(where the bridge exists); the eventual proof instantiates `h` with the holomorphic Weierstrass
polynomial over the germ ring (Phase B). This de-risks Phase D — confirms "witness order-inv ⟹
disc order-inv" closes with what we have. NOTE: the *analytic* version of the bridge for the germ
setting is largely available too (`order_additivity_holomorphic` for open sets +
`complexify_order_invariant` to lift section-order to an open complex nbhd).

**Next per plan:** Phase B (analytic germ-ring substrate `𝒪ₙ` + its valuation), which D2 instantiates
over; then the two mountains C (convergent Weierstrass) and E (Zariski).

### B1 STARTED (2026-05-30): `AnalyticGerm` (new file Generalized/AnalyticGerm.lean) — 0 custom axioms
`𝒪ₙ := AnalyticGerm n` is the **subring of germs at `0 ∈ ℂⁿ`** admitting an analytic representative
(carrier `{g | ∃ f, AnalyticAt ℂ f 0 ∧ ↑f = g}`), a `Subring (Filter.Germ (𝓝 0) ℂ)` — hence a
`CommRing` (`example : CommRing (AnalyticGerm n) := inferInstance` checks). Closure under +,·,−,0,1
from `AnalyticAt.add/mul/neg` + `analyticAt_const`. Germs are the right object: Weierstrass gives a
factorization on an *arbitrarily small* nbhd, which germs quotient out.

This is the **CommRing core of B1** — enough to host the Weierstrass polynomial `h ∈ 𝒪ₙ[t]` and
`norm_identity_elim`.

### B1 COMPLETE (2026-05-30): `IsLocalRing (AnalyticGerm n)` — 0 custom axioms
`𝒪ₙ` is a **local ring**. Helper `AnalyticGerm.isUnit_of_rep_ne_zero`: a germ with an analytic
representative `g` with `g 0 ≠ 0` is a unit (pointwise inverse `g⁻¹` is analytic at `0` via
`AnalyticAt.inv`, and `g · g⁻¹ =ᶠ 1` near `0`, so the germs are inverse). Locality via
`IsLocalRing.of_isUnit_or_isUnit_one_sub_self`: for any germ `a` with rep `f`, either `f 0 ≠ 0`
(`a` is a unit) or `f 0 = 0` (then `(1-f) 0 = 1 ≠ 0`, so `1 - a` is a unit). `#print axioms` →
`[propext, Classical.choice, Quot.sound]`. (Needed `import Mathlib.RingTheory.LocalRing.Basic`.)

### B2 COMPLETE (2026-05-30): germ valuation `AnalyticGerm.order` + multiplicativity — 0 custom axioms
The **vanishing order / valuation** on `𝒪ₙ`: `AnalyticGerm.order n b := order ℂ (rep b) 0` for a
chosen analytic representative. Well-definedness bridge **`AnalyticGerm.order_eq_order_rep`**: the
value equals `order ℂ f 0` for *any* analytic rep `f` (`↑f = b.1`), proved via a field-generic
`order_congr_of_eventuallyEq'` (germ-only dependence of `order`) — the plan's B2 target
`holGerm_order_eq_order`. Valuation property **`AnalyticGerm.order_mul`**:
`v(a·b) = v(a) + v(b)`, from `order_mul_analytic`.

**Refactor:** `order_mul_analytic` (+ its 5 helpers: `order_eq_top_of_eventuallyEq_zero`,
`eventuallyEq_zero_of_order_eq_top`, `symmetric_multilinear_eq_zero_of_diagonal_zero`,
`analyticAt_line_restriction`, `iteratedDeriv_line_eq_iteratedFDeriv_diag`) **relocated** from
`Generalized/Lifting.lean` into new low-level file **`Mccalum/OrderMulAnalytic.lean`** (made public)
so `AnalyticGerm` can reuse them without an import cycle. Full library rebuilds clean.

**Phase B (germ-ring substrate) is now complete:** CommRing core + IsLocalRing + valuation. Then
`disc_order_invariant_of_witness` (D2) can be re-run with `R := 𝒪ₙ`. Remaining: the two mountains
**C (convergent Weierstrass)** and **E (Zariski)**, plus optional B3 (Cauchy/majorant for C).

## STRATEGY PIVOT (2026-05-30): isolate C & E as two clean axioms, prove A+B+D+F

Per user direction: replace the single monolithic axiom `analytic_pseudopoly_delineable_nonsep`
with **two crisp, citable classical axioms** (convergent Weierstrass + Zariski) and **prove the
connective phases A, D, F** (B already done) against them. Net effect: the main theorem reduces to
depending only on those two axioms + standard. This is a strict honesty improvement (one bespoke
axiom → two named classical theorems + fully-proved glue) and pins the C/E interfaces precisely,
before attacking them later. **Bonus:** isolating C as an axiom means **B3 (Cauchy/majorant) is no
longer needed** (it only served to prove C's convergence). Remaining connective work: A2, A3, D1,
D2 (reuse), D3, F1 (reuse Schwarz), F2, F3. Main risk: A2 (root-count continuity, absent in
Mathlib) is the one nontrivial real-analysis connective piece.

### Axiom interfaces DRAFTED (2026-05-30): `Mccalum/Generalized/WeierstrassZariskiAxioms.lean`
Type-checks; both register as proper axioms. **Function-level** (coefficients/roots as `AnalyticAt ℂ`
functions), decoupled from the germ ring (which stays a Phase-D internal). Helpers `CParam s e`
(`= ℂˢ × ℂᵉ`, section `T = ℂˢ × {0}`), `weierstrassPoly m a w` (`= tᵐ + ∑ aᵢ(w)tⁱ`),
`weierstrassDiscFn`.
- **`weierstrass_preparation_analytic`**: `G` analytic, `G(0,·)` order exactly `m>0` ⟹
  `G =ᶠ u · (weierstrassPoly m a)` with `u 0 ≠ 0`, `aᵢ` analytic, `aᵢ 0 = 0`.
- **`zariski_root_sections`**: monic Weierstrass `aᵢ` with **disc constant order along `T`**
  (`∀ᶠ y, order ℂ discFn (y,0) = order ℂ discFn 0` — same shape as the real `hP_oi`) ⟹ holomorphic
  sections `ψᵢ : ℂˢ → ℂ`, `ψᵢ 0 = 0`, constant `multᵢ > 0`, `∑ multᵢ = m`, distinct branches, and
  the clean factorization `weierstrassPoly m a (y,0) = ∏ᵢ (X − C(ψᵢ y))^multᵢ` on a **full** nbhd
  (avoids puncture issues; pointwise-distinct roots + `rootMultiplicity` derived in F2).

### Connective chain — D3 core PROVED (2026-05-30): `order_factor_const_of_mul_analytic`
First connective-chain artifact, in `Mccalum/OrderMulAnalytic.lean`, 0 custom axioms. The
**holomorphic, preconnected reverse factor bridge**: if `f, g` are analytic, not ≡0, on a connected
open `U`, and `f·g` has **constant vanishing order along a preconnected `S ⊆ U`** (basepoint
`z₀ ∈ S`), then `f` and `g` each have constant order along `S`. This is the `order ℂ` analogue of
`order_invariant_factor_of_mul` (polyOrder) and the preconnected generalization of
`order_additivity_holomorphic` (the `S = U` open case). **It is Phase D3's engine**: the witness
forces `order(P)` constant along the section, the norm identity gives `P^m = ±disc(h)·Q`, and this
peels off `disc(h)`. Companion `order_pow_analytic` (`order(fᵐ) = m·order f`) added for the D3
application (`P^m`).

**Supporting refactor:** relocated the 3 analytic-order USC helpers
(`order_ne_top_of_ne_zero`, `isOpen_order_le_inter`, `isOpen_order_lt_inter`) from `Lifting.lean`
into `OrderMulAnalytic.lean` (now **public**, and the two `isOpen_*` **generalized** from
`Fin s → ℂ` to any ℂ-normed `E`). `order_additivity_holomorphic` (still in Lifting) now consumes
them via import. Full library rebuilds clean.

### Connective chain — F2 PROVED (2026-05-30): root structure from the Zariski factorization
New file `Mccalum/Generalized/RootSectionsAlgebra.lean`, 0 custom axioms. Pure polynomial algebra
over `ℂ` extracting the per-root facts F3 needs from the Zariski factorization
`weierstrassPoly m a (y,0) = ∏ᵢ (X − C(ψᵢ y))^multᵢ`:
- `isRoot_prod_X_sub_C_pow` / `weierstrass_section_isRoot` — **exhaustiveness**: roots of
  `∏ᵢ (X−C cᵢ)^eᵢ` (eᵢ>0) are exactly the `cᵢ`.
- `rootMultiplicity_prod_X_sub_C_pow` / `weierstrass_section_rootMultiplicity` — **multiplicity**:
  when the `cᵢ` are pairwise distinct, `rootMultiplicity cᵢ₀ = eᵢ₀` (via `rootMultiplicity_mul` +
  `rootMultiplicity_X_sub_C_pow` + `rootMultiplicity_eq_zero` on the cofactor).
The two `weierstrass_section_*` corollaries are stated directly against the Zariski axiom's output
shape (rewrite by the factorization, apply the generic lemma).

### Connective chain — F1 PROVED (2026-05-30): `real_section_of_real_valued` (in Lifting.lean)
0 custom axioms. Phase F1 Schwarz real recovery: a holomorphic section `ψ` real-valued on the real
slice near `x₀` restricts to real-analytic `η := Re∘ψ∘realEmbedding` (via the proven
`real_restriction_analytic`) **and** `(η x : ℂ) = ψ(realEmbedding x)` on the slice — the bridge that
turns the complex Zariski factorization into a real-root statement for F3. Placed in Lifting (where
`realEmbedding`/`real_restriction_analytic` live, and where F3 will assemble).

### Connective chain — evaluation infrastructure PROVED (2026-05-30): `WeierstrassEval.lean`
New file `Mccalum/Generalized/WeierstrassEval.lean`, 0 custom axioms. The norm identity runs over the
**pointwise function ring** `CParam s e → ℂ` (the germ ring is only needed for D1's membership), so
`resultant` of the function-coefficient Weierstrass polynomial **is** a single function. Provides:
- `weierstrassPolyFun m a : (CParam s e → ℂ)[X]` (monic, deg `m`) + `weierstrassPolyFun_map_eval`
  (`Pi.evalRingHom` at `w` recovers `weierstrassPoly m a w`), `weierstrassPoly_monic`,
  `weierstrassPoly_natDegree = m`.
- `weierstrassResFun m a : CParam s e → ℂ` = `resultant(weierstrassPolyFun, derivative)`, with
  `weierstrassResFun_apply` (pointwise = `resultant(weierstrassPoly m a w, …)`) via
  `resultant_map_map` + `derivative_map`.
- `weierstrassResFun_eq_discFn` — for monic, `resultant = (-1)^k · discr` pointwise (`resultant_deriv`).
- `order_weierstrassResFun_eq` — resFun and discFn share vanishing order (sign unit), via the new
  `order_const_mul_analytic`/`order_const_analytic_ne` (added to `OrderMulAnalytic`). **This is the
  bridge from D2's norm identity (yields `resultant`) to the Zariski axiom's hypothesis (uses `discr`).**

With this, the D-phase order argument is fully wired *except* the membership input: applying
`norm_identity_elim (CParam s e → ℂ) (weierstrassPolyFun m a) …` needs `C(P) ∈ ⟨h, h'⟩` (D1, the
germ-ring/subresultant step). Everything downstream of that membership (norm identity → `P^m =
±resFun·Q` pointwise → `order_pow_analytic` + `order_factor_const_of_mul_analytic` along section →
`order_weierstrassResFun_eq` → Zariski's `hdisc`) is now built.

### Connective chain — D1 algebraic core PROVED (2026-05-30): `MembershipTransfer.lean`
New file `Mccalum/Generalized/MembershipTransfer.lean`, 0 custom axioms. The **unit-multiplication
membership transfer** for polynomial ideals (any `CommRing`):
- `mem_span_pair_deriv_of_mul`: `p ∈ ⟨u·h, (u·h)'⟩ ⟹ p ∈ ⟨h, h'⟩` — **no hypothesis on `u`** for this
  inclusion (both `u·h` and `(u·h)' = u'h+uh'` already lie in `⟨h,h'⟩`). This is the half used
  downstream (Weierstrass `g = u·h`, push the witness from `⟨g,g'⟩` into `⟨h,h'⟩`).
- `span_pair_deriv_mul_eq_of_isUnit`: the full ideal equality `⟨u·h,(u·h)'⟩ = ⟨h,h'⟩` when `u` a unit
  (reverse inclusion via `w = u⁻¹`).

**HONEST RESIDUAL (the genuine D1/A3 obstacle, NOT resolved):** the *input* to the transfer — the
complexified/pointwise membership `C(P) ∈ ⟨g_ℂ, g_ℂ'⟩` over the relevant ring — is the hard part.
The real witness `hP_elim` has Bézout cofactors `a(w),b(w)` that are **not analytic** in `w` (chosen
pointwise), so the membership does not complexify directly. The faithful resolution needs the
**subresultant** structure (the elimination ideal is generated by principal subresultant coefficients,
whose Bézout cofactors *are* polynomial in `g`'s coefficients, hence analytic) — and **Mathlib has no
subresultant theory**. This is one of the two genuine research-scale nuts (with A2). The algebraic
*transfer* above is the clean, reusable component that sits on top of that input once obtained.

**Connective-chain status:** A1 done; B done (germ ring); **D3-core, eval-infra, F2, F1, D1-core
done**; axioms C/E drafted. The **"F" output side is complete** (F1+F2); the **D-phase order machinery
is complete modulo the membership input**. Remaining is the A/D **middle** (the connective core) + F3
plumbing:
- **A2** localize at real root (root-count continuity — nontrivial real analysis, absent from Mathlib) — HARD NUT
- **D1-input** complexify the membership: the elimination-ideal cofactors via **subresultant theory**
  (absent from Mathlib) — HARD NUT. (D1 algebraic *transfer* `⟨u·h⟩→⟨h⟩` is DONE.)
- A3 complexify (mostly reuse `analyticAt_complexify`/`complexify_order_invariant`)
- D2-application `norm_identity_elim` over the function ring `CParam s e → ℂ` (direct reuse;
  `weierstrassResFun` already identified — see `WeierstrassEval`)
- D3-application: wire `order_factor_const_of_mul_analytic` + `order_pow_analytic` +
  `order_weierstrassResFun_eq` along the section to produce Zariski's `hdisc` (pieces all built)
- F3 assemble + discharge `analytic_pseudopoly_delineable_nonsep`

**The two genuine research-scale nuts are now isolated: A2 (root-count continuity) and D1-input
(subresultant cofactor complexification). Everything else in the chain is built or is plumbing.**

### D1-input OBSTACLE DISSOLVED (2026-05-30): analytic cofactors are already present
**KEY RESULT.** The "subresultant theory" nut for D1-input was a false alarm. Scoping showed:
- The resultant-Bézout shortcut (`exists_mul_add_mul_eq_C_resultant`) does NOT close D1-input (it gives
  the *resultant's* membership, not the arbitrary witness `P`'s).
- BUT: `mccallum_3_2_3_generalized`'s elimination hypotheses (`hd_mem`/`hr_mem`) are **`Polynomial`-ideal
  memberships over `(MvPolyR n)[X]`** — their Bézout cofactors are polynomials in the variables, hence
  analytic. This stays polynomial down the chain; only at the function-level axiom interface
  (`lifting_generalized_codim_local`, the `hPfull_elim`) is it **weakened** to pointwise membership,
  *discarding* the cofactors `a.map (eval (Φ.symm ·))`, `b.map (...)` that the proof already builds.

**VERIFIED IN LEAN (soundness check (a)):** added `hPfull_elim_strong` in
`lifting_generalized_codim_local` proving the **analytic-cofactor form** is derivable in-context
(cofactor coeffs `w ↦ eval (Φ.symm w) (a.coeff k)` analytic, same argument as `hgfull_coeff_an`).
Full library builds; `mccallum_3_2_3_generalized` axiom set unchanged.

**Consequence:** strengthening the axiom `analytic_pseudopoly_delineable_nonsep`'s `hP_elim` to the
analytic-cofactor form is **sound** — no hypothesis of the main theorem changes; the call site
supplies it. D1-input drops from "research-scale subresultants" to **bounded plumbing**. Honest
caveat (the remaining D1 residual): transferring the analytic-cofactor membership of `g` to the
*monic local factor* `h` over the *polynomial* ring `𝒪ₙ[t]` (for `norm_identity_elim`) still rides on
**Weierstrass division** (part of the C-axiom package), since `g = u·h` lives in the germ ring
`𝒪ₙ₊₁`, not `𝒪ₙ[t]`. That is plumbing on the C axiom, not a new mathematical nut.

**Net: only ONE genuine research-scale nut remains — A2 (root-count continuity).**

### C-axiom WIDENED (2026-05-30): Weierstrass division added to `WeierstrassZariskiAxioms.lean`
Added `weierstrass_division_analytic` (existence: any analytic `F = q·h + r`, `r` a degree-`<m`
polynomial-in-`t` with analytic coeffs) and `weierstrass_division_unique` (the only division of the
zero germ is trivial). Both register as proper axioms; full library builds. Division is the classical
companion of `weierstrass_preparation_analytic` (it follows from preparation), so this is a faithful
widening of the C-axiom package — not a new mathematical commitment.

**Purpose (closes the D1 residual):** these two axioms are *exactly sufficient* for the
germ-ring → `𝒪ₙ[t]` descent. Sketch: from `C(P) = γ·h + δ·h'` in the germ ring `𝒪ₙ₊₁`, divide
`γ, δ` by `h` (existence) → `C(P) = (rᵧ + k)·h + r_δ·h'` with `rᵧ, r_δ` polynomial and `k·h` equal to
a polynomial `P₀`; polynomial-divide `P₀ = q_poly·h + r_poly` in `𝒪ₙ[t]`, then
`(k − q_poly)·h − r_poly =ᶠ 0` and **uniqueness** forces `r_poly = 0`, `k =ᶠ q_poly` (polynomial). So
`C(P) ∈ ⟨h, h'⟩` over `𝒪ₙ[t]`, and `norm_identity_elim` applies. The interface (existence+uniqueness)
is verified-by-reasoning to be the right shape; the full Lean derivation of the descent (with the
germ↔`weierstrassPolyFun` eval translations) is the remaining bounded plumbing.

**C-axiom package now:** `weierstrass_preparation_analytic`, `weierstrass_division_analytic`,
`weierstrass_division_unique`. **E-axiom:** `zariski_root_sections`. These are the only non-standard
ingredients the finished proof will rest on (all classical, citable theorems).

### D1 descent — FOUNDATION built (2026-05-30): `WeierstrassDivision.lean`
New file, all lemmas build, axiom-clean (uniqueness depends only on the division axiom). The
load-bearing **polynomial ↔ germ translation** for the descent:
- `polyToFun : (CParam s e → ℂ)[X] →+* (CParam s e × ℂ → ℂ)` (`X↦t`, `C c ↦ (z,t)↦c z`), with
  `polyToFun_apply` (pointwise `= (p.map (eval z)).eval t`) and `polyToFun_weierstrassPolyFun`
  (sends `weierstrassPolyFun` to the Weierstrass-poly-as-germ).
- **`polyToFun_coeff_eventuallyEq_zero`** — germ-injectivity: `polyToFun p =ᶠ 0 ⟹ ∀ k, p.coeff k =ᶠ 0`
  (for fixed `z`, `t ↦ polyToFun p (z,t)` is a `ℂ`-poly vanishing on a nbhd ⟹ `0`, via
  `eq_zero_of_infinite_isRoot` + `infinite_of_mem_nhds`). The descent's return trip germ → `𝒪ₙ[t]`.
- **`weierstrass_division_unique'`** — full two-divisions uniqueness from the zero-germ axiom.

### D1 descent — CORE STEP PROVED (2026-05-30): `analytic_mul_weierstrass_eq_poly`
The hardest part of the assembly. In `WeierstrassDivision.lean`, builds, depends only on
`weierstrass_division_unique` (+ standard). **"An analytic germ `k` with `k·h =ᶠ polyToFun P₀` (P₀ a
polynomial, h monic Weierstrass) is itself a polynomial germ: `k =ᶠ polyToFun (P₀ /ₘ h)`."** Proof:
polynomial-divide `P₀ = h·Q₀ + R₀` (`modByMonic`), then `(k − polyToFun Q₀)·h + ∑(−R₀.coeffᵢ)tⁱ =ᶠ 0`
is a division of zero, and `weierstrass_division_unique` forces `k =ᶠ polyToFun Q₀`. The
**divByMonic-analyticity** facts (`polyToFun (P₀/ₘh)` analytic, `(P₀%ₘh).coeffᵢ` analytic) are taken as
hypotheses — the precise remaining obligation. Helper `polyToFun_eq_finSum_of_natDegree_lt` (a
degree-`<m` poly's `polyToFun` is the `Fin m` sum, matching the division-axiom remainder shape) added.

**Remaining descent assembly (now small + isolated):**
1. **divByMonic-analyticity** — `/ₘ`,`%ₘ` by the analytic monic `h` preserve analytic coefficients.
   Route: the analytic-germ ring over `CParam s e` (parallel to Phase B's `AnalyticGerm`) + the proven
   Mathlib `map_divByMonic`/`map_modByMonic`. Discharges the two hypotheses of the core step.
2. **`u`-transfer** — `g = u·h` ⟹ germ membership `C(P) ∈ ⟨h,h'⟩` (a `=ᶠ`/germ form of the proven
   `mem_span_pair_deriv_of_mul`, with `∂_t` a derivation), giving the `k·h =ᶠ polyToFun P₀` input.
3. **assemble** — combine (1)+(2)+core step + `polyToFun_coeff_eventuallyEq_zero` (injectivity) into
   the `𝒪ₙ[t]`-membership, then `norm_identity_elim` applies and Phase D closes against the C/E axioms.

**Descent foundation + core are done and building; only the analyticity lemma + `u`-transfer +
final glue remain — all bounded, no new mathematical content.**

### D1 descent — STEP 1 COMPLETE (2026-05-30): divByMonic-analyticity discharged
In `WeierstrassDivision.lean`, all axiom-clean. The key realization: **`{f | AnalyticAt ℂ f 0}` is a
`Subring`** of the function ring (`AnalyticAtSubring`), so `map_divByMonic`/`map_modByMonic` over it
give analyticity preservation directly — no germ ring needed.
- `coeff_divByMonic_analyticAt` — `/ₘ`,`%ₘ` by a monic with analytic coeffs preserve analytic coeffs
  (via `Polynomial.toSubring` + `Injective.monic_map_iff` + `map_divByMonic`).
- `polyToFun_analyticAt` — `polyToFun` of an analytic-coeff polynomial is analytic
  (finite sum of `(coeffᵢ∘fst)·sndⁱ`).
- `weierstrassPolyFun_coeff_analyticAt` — the Weierstrass polynomial's coefficients are analytic.
- **`analytic_mul_weierstrass_eq_poly_of_coeffs`** — the core descent step **fully discharged**: needs
  only `P0` analytic-coeffs (the divByMonic-analyticity is derived). Depends only on
  `weierstrass_division_unique` (+ standard).

**Descent status: foundation + core step DONE (self-contained).** Remaining: **Step 2** the `u`-transfer
(`g = u·h` ⟹ the `k·h =ᶠ polyToFun P₀` germ input, a `=ᶠ` form of `mem_span_pair_deriv_of_mul`), and
**Step 3** final glue (combine + `polyToFun_coeff_eventuallyEq_zero` ⟹ `𝒪ₙ[t]` membership ⟹
`norm_identity_elim`).

### D1 descent — MEMBERSHIP DESCENT (Step 3a) PROVED (2026-05-30): `MembershipDescent.lean`
`theorem membership_descent` builds, axiom-clean (only the two Weierstrass-division axioms). From a
**germ-level membership** `polyToFun (C P) =ᶠ Γ·H + Δ·H'` (`Γ,Δ` analytic), it produces **polynomial
cofactors** `A,B` with analytic coefficients and `polyToFun (C P) =ᶠ polyToFun (A·h + B·h')`. Method:
Weierstrass-divide `Γ,Δ` → analytic quotients + degree-`<m` remainder polys (`remPoly`); collect
`k := qΓ·H + qΔ·H'`; show `k·H =ᶠ polyToFun P₀`; apply the core step
(`analytic_mul_weierstrass_eq_poly_of_coeffs`) ⟹ `k` polynomial; assemble `A := P₀/ₘh + rΓ`, `B := rΔ`.
Support: `remPoly` + lemmas; `AnalyticCoeffs` predicate closed under `+,−,*,C,derivative,/ₘ` (all
proved, via the `AnalyticAtSubring` + `coeff_mul`/`Finset.analyticAt_fun_sum` machinery).

### D1 descent — STEP 2 (`u`-transfer) DONE (2026-05-30): `MembershipDescent.lean`
`theorem u_transfer` (axiom-clean, pure algebra) + `theorem descent_membership` (combines Step 2 +
Step 3a; depends only on the two Weierstrass-division axioms). `u_transfer`: from the analytic-cofactor
membership `C P = A·g + B·g'` and the **differentiated Weierstrass factorization** `polyToFun g =ᶠ u·H`,
`polyToFun g' =ᶠ uder·H + u·H'` (the prep axiom + Leibniz in `t`, taken as hypotheses), produces the
germ membership `polyToFun (C P) =ᶠ Γ·H + Δ·H'` (`Γ := polyToFun A·u + polyToFun B·uder`,
`Δ := polyToFun B·u`). `descent_membership` chains it into `membership_descent` for the full output
`polyToFun (C P) =ᶠ polyToFun (A'·h + B'·h')` with analytic cofactors.

### D1 descent — STEP 3b FULLY PROVEN (2026-05-30): `DescentNormIdentity.lean` — 0 sorries, axiom-clean
`theorem descent_norm_identity` is **fully proven**; `#print axioms` → `[propext, Classical.choice,
Quot.sound]` only (NO `sorryAx`, no custom axioms — it takes the descent membership as a hypothesis and
uses the proven `norm_identity_elim`). From `descent_membership`'s `=ᶠ` membership it produces
`P^m =ᶠ weierstrassResFun·Q` (`Q` analytic) — the exact `hnorm` input of
`DiscOrder.weierstrassDisc_order_const_along_section`. Built: the **analytic-germ ring `AnalyticGermP`
on `CParam`** (Subring of `Germ (𝓝 0) ℂ`; + `CharZero` instance) + `germHom` + `analyticCoeffs_germ_mem`.
Proof chain: `polyToFun`-injectivity ⟹ coefficient-wise germ equality ⟹ `toSubring` to `𝒪[X]` ⟹
`norm_identity_elim` over `𝒪` ⟹ map back via `𝒪.subtype` + `resultant_map_map`(×2) + `Germ.coe_eq`
cast. The two former bookkeeping gaps are now discharged: `hdSnd` (`(derivative hS).natDegree = m−1`
via `CharZero ↥𝒪`) and `hres` (resultant degree-arg `(m,m−1)` matching via `resultant_map_map`).

**DESCENT STATUS — COMPLETE end-to-end, FULLY PROVEN, SORRY-FREE.** Chain:
`descent_membership` (Steps 2+3a, axiom-clean modulo the C-division axioms) → `descent_norm_identity`
(Step 3b, axiom-clean) → `DiscOrder.weierstrassDisc_order_const_along_section` (D3-app, ✅) → Zariski's
`hdisc`. **The entire Phase-D pipeline is built, sorry-free, and type-checks against the C/E axioms.**

### Single-cluster composition — STARTED (2026-05-30): back half + analyticity helpers
- **`ClusterRootStructure.lean`** `cluster_root_structure` (axiom-clean modulo `zariski_root_sections`):
  the **back half** `Zariski → F2`. From constant disc order along the section, produces the holomorphic
  root sections `ψᵢ` + full root/multiplicity structure (exhaustiveness everywhere near `0`; multiplicity
  wherever the `ψᵢ` are distinct).
- **`WeierstrassResAnalytic.lean`** `weierstrassResFun_analyticAt`, `weierstrassDiscFn_analyticAt`
  (axiom-clean): the resultant/disc functions of the family are analytic at `0` — via the `toSubring` +
  `resultant_map_map` technique (resultant of analytic-coeff polys lands in `AnalyticAtSubring`); `discFn`
  follows as `(-1)^k · resFun`. These discharge the `hres_an`/`hdisc_an` hypotheses of `DiscOrder`.

### Single-cluster composition (complex) — COMPLETE (2026-05-30): `SingleCluster.lean`
`theorem single_cluster_complex` builds, axiom-clean modulo `zariski_root_sections`. **The entire
complex single-cluster chain, fully wired and sorry-free:** from the descent's norm identity
(`P^m =ᶠ weierstrassResFun·Q`, `Q` analytic) + the witness's constant section-order, it produces the
holomorphic root sections `ψᵢ` of the section Weierstrass polynomial + their full root/multiplicity
structure. The **front-half glue**: builds open metric balls `U`/`V` (analytic + norm-identity nbhd,
`AnalyticAt → AnalyticOnNhd` via `eventually_analyticAt`, `isConnected_ball`); derives the
non-vanishing of `resFun`/`Q` from `P ≢ 0` (`order P 0 ≠ ⊤` ⟹ `∃ z, P z ≠ 0` ⟹ via `P^m=resFun·Q`);
runs `DiscOrder`; chains `cluster_root_structure` (Zariski + F2).

**STATUS: the WHOLE D→E→F-root pipeline is built and verified end-to-end** —
`descent_membership` → `descent_norm_identity` → `single_cluster_complex` (the latter chaining
`DiscOrder` + `cluster_root_structure` = Zariski + F2). Only `zariski_root_sections` (E) and the
C-division axioms remain as the non-standard ingredients on this path.

### F1 per-section recovery DONE (2026-05-30): `RealRecovery.lean`
`real_root_function` (axiom-clean): a complex section `ψ` analytic at `0`, `ψ 0 = 0`, real on the real
slice ⟹ real-analytic `η := Re∘ψ∘realEmbedding`, `η 0 = 0`, recovery `(η x:ℂ)=ψ(realEmbedding x)`.
(Un-privated `realEmbedding`/`realEmbedding_apply`/`realEmbedding_single` in Lifting.)

### A3 plumbing — family↔function-ring bridge DONE (2026-05-30): `PolyOfFamily.lean`
`polyOfFamily`/`polyToFun_polyOfFamily` (axiom-clean): assemble a degree-`≤N` family `gℂ : CParam→ℂ[t]`
into a function-ring polynomial `g : (CParam→ℂ)[X]` with `polyToFun g (z,t) = (gℂ z).eval t`. Connects
the complexification output to the `polyToFun`-based descent inputs.

**Existing complexification tools (reuse):** `analyticAt_complexify` (real f ⟹ complex `f_ℂ` analytic +
real-on-slice + **order-preserving** `order ℂ f_ℂ = order ℝ f`), `complexify_pseudopoly` (real family ⟹
`gℂ : ℂᵐ→ℂ[t]` analytic + real-on-slice), `complexify_order_invariant` (real-slice order μ ⟹ complex
order μ near 0).

### A3 friction #1 (product↔`Fin` reconciliation) DONE (2026-05-30): `OrderCLE.lean` + `ProductComplexify.lean`
The reindexing reconciliation that moves the complexification machinery onto the *product* base
`CParam s e = (Fin s→ℂ)×(Fin e→ℂ)`. All axiom-clean.
- `order_comp_continuousLinearEquiv` (`OrderCLE.lean`): `order 𝕜 (f ∘ g) x = order 𝕜 f (g x)` for any
  CLE `g` (via `iteratedFDeriv_comp_continuousLinearEquiv` + `continuousMultilinearMapCongrLeft`
  injectivity). General `𝕜`, fully reusable.
- `reindexCLE 𝕜 s e : (Fin (s+e)→𝕜) ≃L[𝕜] (Fin s→𝕜)×(Fin e→𝕜)` + `reindexCLE_apply` (rfl-characterised)
  + `reindexCLE_ofReal` (commutes with coordinatewise `ofReal`).
- `analyticAt_complexify_prod`: real-analytic `F` on the product base ⟹ holomorphic `F_ℂ` on
  `CParam`, real-slice agreement, **order preservation at 0** (`order ℂ F_ℂ 0 = order ℝ F 0`). Built by
  transporting `analyticAt_complexify` across `reindexCLE` (order half uses the CLE lemma).
- `complexify_pseudopoly_prod`: the family version (`g : product → ℝ[t]` ⟹ `gℂ : CParam → ℂ[t]`),
  mirroring `complexify_pseudopoly` coefficientwise.

### A3 friction #2 (section-order complexification) DONE (2026-05-30): `SectionOrder.lean`
`complexify_section_order_invariant` (axiom-clean): real witness `P` with constant order `μ` **along
the section** `{(y,0)}` near `0` + complexification `Pℂ` (analytic, real-slice agreement,
`order ℂ Pℂ 0 = μ`) ⟹ `∀ᶠ y in 𝓝 0, order ℂ Pℂ (y,0) = μ` (the **full** CParam order at section
points — exactly the `hP_oi` `DiscOrder`/`single_cluster_complex` consume). Structure mirrors
`complexify_order_invariant`: USC upper bound (`isOpen_order_le_inter` pulled back through the section
inclusion) + identity-theorem lower bound applied in the **section variable** `y`. Supporting lemmas
(all axiom-clean): `prodEmbedCLM`, `cml_eq_zero_of_real_inputs` / `cml_eq_zero_of_reindex_basis`
(CParam multilinear-vanishing, transported via `reindexCLE` from the `Fin (s+e)` basis lemma),
`cderiv_zero_at_real_point` (full ℂ-derivative vanishes at real section points — chain rule +
`restrictScalars` + the CParam-basis lemma). Un-privated `cml_eq_zero_of_basis_eq_zero` and
`order_eq_top_of_real_eq_zero` in Lifting for reuse.

### A3 friction #3 (factorization differentiation + cluster assembly) DONE (2026-05-31): `FactorDifferentiate.lean` + `ClusterAssembly.lean`
The genuine analytic content of friction #3 was the **`hfac'` derivation** — differentiating the
C-axiom factorization `polyToFun g =ᶠ u · polyToFun h` in `t` to get the product-rule form
`descent_membership` consumes. `FactorDifferentiate.lean` (axiom-clean):
- `ptderiv F (z,t) = deriv (τ ↦ F (z,τ)) t` (partial `t`-derivative) + `ptderiv_polyToFun`
  (`ptderiv (polyToFun p) = polyToFun (derivative p)`, via `Polynomial.hasDerivAt` + `derivative_map`).
- `ptderiv_congr` (germ-only dependence, for `=ᶠ` differentiation), `ptderiv_mul` (product rule),
  `analyticAt_ptderiv` (`ptderiv u` analytic via `AnalyticAt.fderiv` + eval).
- `factor_deriv`: assembles all of the above into the `hfac'` bridge with `uder = ptderiv u`.

`ClusterAssembly.lean`: `single_cluster_from_weierstrass` wires the **whole** per-cluster chain —
`factor_deriv` → `descent_membership` → `descent_norm_identity` → `single_cluster_complex` — taking
the C-axiom factorization `hfac`, the complexified polynomial elim membership `C Pℂ = A·g + B·g'`,
`hP_ne`, and the section order `hP_oi` as inputs, producing the holomorphic root sections + multiplicity
structure. **Depends only on the named classical axioms C and E** (`weierstrass_division_analytic`,
`weierstrass_division_unique`, `zariski_root_sections`) + standard — no custom/sorry axioms.

### A3 item (b) (membership complexification) DONE (2026-05-31): `MembershipComplexify.lean`
`complexify_membership` (axiom-clean): lifts the **real analytic-cofactor** elimination membership
`C(P w) = A w·g w + B w·g'(w)` (near 0) to the **eventual `polyToFun`** form
`polyToFun (C Pℂ) =ᶠ polyToFun Aℂ·polyToFun g + polyToFun Bℂ·polyToFun g'` consumed by
`single_cluster_from_weierstrass`. Inputs: the complexified function-ring polynomials with
`Polynomial.map`-level real-slice agreements + the real identity. The exact global function-ring
identity is *not* achievable (complexification is local), so the target is the eventual form — this
required **weakening** `u_transfer`/`descent_membership`/`single_cluster_from_weierstrass`'s `hmem_g`
from an exact polynomial identity to the eventual `polyToFun` form (a strict generalization, not an
added hypothesis; only my own A3 code calls them). Supporting (axiom-clean):
- `eventuallyEq_zero_of_real_eq_zero_prod` (`SectionOrder.lean`): **CParam identity theorem** — analytic
  `h : CParam → ℂ` vanishing on the real slice near 0 vanishes near 0. Transported from
  `order_eq_top_of_real_eq_zero` via `reindexCLE` (no new derivative machinery).
- `polyToFun_eventuallyEq_zero_of_coeffs`: coefficient-wise-zero ⟹ `polyToFun`-zero, both near 0.
Proof works at the `Polynomial.map` level (the difference poly `D` satisfies `D.map(eval at real pt)=0`
from the real identity ⟹ each `D.coeff k` vanishes on the real slice ⟹ near 0 ⟹ `polyToFun D =ᶠ 0`).

### A3 CLOSED (2026-05-31): `ClusterFromReal.lean` (+ `ComplexifyGlue.lean`)
`cluster_from_real` is the **complete A3 front-end**: from the real section family `g`, witness `P`,
analytic cofactors `A,B` + elimination membership, real section-order invariance, and the per-cluster
**localization datum** (`analyticOrderAt ((g 0) complexified) 0 = m`, the multiplicity of the cluster
root at `t=0`), it constructs *every* input of `single_cluster_from_weierstrass` and produces the
holomorphic root sections + multiplicity structure. **Depends only on the named classical axioms C and
E** + standard — no custom/sorry axioms. Composition:
`complexify_pseudopoly_prod`/`analyticAt_complexify_prod` → `map_agree_of_complexify` /
`analyticCoeffs_polyOfFamily` glue → `complexify_membership` (item b) →
`weierstrass_preparation_analytic` (C axiom, item a; order datum transferred via `polyToFun_apply`) →
`complexify_section_order_invariant` → `single_cluster_from_weierstrass`.

**Localization fix (2026-05-31):** the complexification is only *locally* analytic (`AnalyticAt`, not
global), so `cderiv_zero_at_real_point` and `complexify_section_order_invariant` were re-localized to
accept `AnalyticOnNhd ℂ Pℂ U` on an open `U ∋ 0` (extracted via `eventually_analyticAt`), using the
`iteratedFDerivWithin` chain rule on `U` instead of the global `ContDiff` one.

### Localization datum internalized DONE (2026-05-31): `AnalyticOrderPoly.lean`
`analyticOrderAt_polynomial_eval` (axiom-clean): for `p : ℂ[X]`, `p ≠ 0`,
`analyticOrderAt (p.eval ·) z₀ = p.rootMultiplicity z₀` (via `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
+ `analyticOrderAt_eq_natCast`); `_ofReal` corollary via `eq_rootMultiplicity_map`. `cluster_from_real`
now takes the clean real hypothesis **`(g 0).rootMultiplicity 0 = m`** (deriving the `analyticOrderAt`
datum internally) — its last non-structural input is gone.

### A2 axiom drafted (2026-05-31): `A2Axiom.lean`
`real_delineation_of_complex_sections` — the **complex→real recovery** axiom (the one remaining
classical real-analysis ingredient, alongside C and E). Takes the holomorphic cluster sections `ψ_i`
that `cluster_from_real` (= Weierstrass + Zariski) produces + the real family, and yields the **real**
root delineation of one cluster (ordered real-analytic `η_i`, ball-localized at the cluster, constant
multiplicities). **Design note:** stated to *consume* the complex sections specifically so C and E stay
load-bearing — the final theorem then rests on `{C, E, A2}`, not `{A2}` (a self-contained per-cluster
real-delineation axiom would have left C/E as mere soundness witnesses).

### F3 build STARTED (2026-05-31): `F3.lean`
Foundational covering-transfer pieces (axiom-clean):
- `isRoot_eq_of_unit_factor`: a unit factor (`u 0 ≠ 0`) doesn't change zeros near `0` — transfers root
  statements across the `u`-Weierstrass factorization.
- `cover_of_weierstrass`: **the core bridge** — from `cluster_from_real`'s data (`u`-factorization
  `hfac`, the `weierstrassPoly`↔`ψ` covering `hroots`, and the section-level map agreement), the
  complex roots of the complexified section family `(fam y).map ℝ→ℂ` within a cluster radius `δ₀` are
  exactly `{ψ_i(realEmbedding y)}` — i.e. A2's `hcover` hypothesis. (Chains: agreement → unit-factor →
  `polyToFun_weierstrassPolyFun` → `hroots`, with the ball-localization plumbing.)

- `multmatch_of_weierstrass` (2026-05-31): the **multiplicity analog** — the multiplicity of a section
  root `ψ_i(realEmbedding y)` in `(fam y).map ℝ→ℂ` equals `mult i`. Built on a clean new lemma
  `analyticOrderAt_eq_of_unit_factor` (order is invariant under a non-vanishing unit factor) +
  `analyticOrderAt_polynomial_eval` (order = rootMultiplicity). Both `cover_of_weierstrass` and
  `multmatch_of_weierstrass` are axiom-clean — they produce exactly A2's `hcover` and `hmult_match`.

### SINGLE-CLUSTER `{C, E, A2}` MILESTONE (2026-05-31): `ClusterCover.lean` + `F3.lean`
> **SUPERSEDED (later 2026-05-31):** the A2 axiom referenced below
> (`real_delineation_of_complex_sections`) was found unsound and removed; `single_cluster_real_delineation`
> now rests on `{C, E, A2′ = real_cluster_single_branch}` + the proved recovery core. See the top section.
`single_cluster_real_delineation` (`F3.lean`) — the **complete per-cluster real delineation**: from the
real product family `g` localized at a multiplicity-`m` cluster root of `g(0,0)` at `t=0`, the real
roots of `g(·,0)` near `0` form finitely many ordered real-analytic functions with constant
multiplicities. **`#print axioms` = exactly `{C, E, A2}`** (`weierstrass_preparation/division/division_unique`,
`zariski_root_sections`, `real_delineation_of_complex_sections`) + standard. The `{C,E,A2}` architecture
is now realized end-to-end for one cluster.
- `ClusterCover.lean`: the three bridges (`isRoot_eq_of_unit_factor`, `cover_of_weierstrass`,
  `multmatch_of_weierstrass`), moved below `ClusterFromReal` to avoid an import cycle.
- `cluster_from_real` enriched: now also outputs the A2-ready `hmult_match` and `⟨δ₀, hcover⟩`
  (computed internally via the bridges), plus takes a section degree-constancy hypothesis.
- `single_cluster_real_delineation` = `cluster_from_real` (enriched) → **A2**.

### Multi-cluster assembly STARTED (2026-05-31): `ShiftCluster.lean`
Translation infrastructure for applying the single-cluster machinery (stated at `t=0`) at a general
real root `t_j` via `taylor t_j (g w) = (g w).comp (X + C t_j)`. **Mathlib already supplies the shift
facts:** `Polynomial.rootMultiplicity_eq_rootMultiplicity` (`p.rootMultiplicity t = (taylor t p).rootMultiplicity 0`),
`natDegree_taylor`, `taylor_apply`/`taylor_X_pow` (ring/linear structure), `derivative_comp` (chain
rule for `g_j' = taylor t_j g'`). The one new ingredient — `analyticAt_taylor_coeff` (the shifted
coefficients stay analytic, axiom-clean) — is built here.

### Step 1 (translation) DONE (2026-05-31): `MultiCluster.lean`
`single_cluster_real_delineation_at` — `single_cluster_real_delineation` at a **general** real root
`t_j`: Taylor-shift `g`,`A`,`B` by `taylor t_j`, apply the `t=0` result, shift the conclusion back
(`η_i + t_j`, ball `|α - t_j| < δ`). Axiom-clean on `{C, E, A2}`. Shift helpers in `ShiftCluster.lean`:
`analyticAt_taylor_coeff` (general domain), `derivative_taylor`, `rootMultiplicity_taylor`,
`eval_taylor`; the multiplicity/degree facts (`rootMultiplicity_eq_rootMultiplicity`, `natDegree_taylor`)
come straight from Mathlib. **A simple root (`m=1`) is just the `m=1` case, so `_at` handles every root
uniformly — no separate IFT branch needed.**

### STEPS 2–3 DONE (2026-05-31): `multi_cluster_real_delineation` (`MultiCluster.lean`)
The **full multi-cluster real delineation** — the real roots of `g(·,0)` near `0` form finitely many
ordered real-analytic functions (one per distinct real root of `g(0,0)`) with constant multiplicities.
**`#print axioms` = exactly `{C, E, A2}`** + standard. This is the conclusion shape of
`analytic_pseudopoly_delineable_nonsep`, now *proven* (not axiomatized) modulo `{C, E, A2}`.

Key design move that made it tractable: **A2 reformulated to output one function per cluster** (the
stable cluster's single root, with `η 0 = 0`), so `single_cluster_real_delineation_at` is structurally
identical to the separable case's IFT-per-root. The glue then mirrors the proven
`separable_family_locally_delineable` almost verbatim: enumerate distinct real roots (`orderIsoOfFin`),
apply `_at` per root, **no-escape** via the Cauchy-bound + tube-lemma compactness argument (reusing
`fam_eval_continuousOn`, `generalized_tube_lemma`, `cauchyBound`), assemble covering + ordering +
multiplicities. (A2's one-function output is sound: under constant disc order a cluster is one stable
root of multiplicity `m`.)

### New dispatcher proved on `{C, E, A2}` (2026-05-31): `Delineable.lean`
`analytic_pseudopoly_delineable'` — the delineation as a **theorem** (separable → IFT
`separable_family_locally_delineable`; non-separable → `multi_cluster_real_delineation`), taking the
strengthened hypotheses (degree bound `Ng`, analytic cofactors `A,B`). `#print axioms` = exactly
`{C, E, A2}`. This is the drop-in replacement for the `analytic_pseudopoly_delineable` axiom-dispatcher.

**Final connection (the only thing between here and `mccallum_3_2_3_generalized` on `{C, E, A2}`):**
an **import-cycle** blocks it in place — `lifting_generalized_codim_local` (which calls the dispatcher)
lives in `Lifting.lean`, *below* the `{C,E,A2}` stack, so it can't see `analytic_pseudopoly_delineable'`
(high). Resolution: relocate the upper chain (`lifting_generalized_codim_local` → `…_codim_case` →
`lifting_theorem_generalized'`, ~550 lines) into a high file importing `MultiCluster`, redirecting the
dispatcher call to `analytic_pseudopoly_delineable'` and supplying its hypotheses at the call site
(verified tractable: `Ng = f.natDegree` via `natDegree_map_le`; cofactors `a,b` from `Ideal.mem_span_pair`
on `hP_mem`, already built as `hPfull_elim_strong`). The relocation is mechanical but large; do it after
committing (the upper chain uses the `{n}` variable + chart/complexify internals — all public, available
via `import Lifting`). The **mathematics is complete**: the delineation is fully proven on `{C, E, A2}`.

### F3 plan (to discharge `analytic_pseudopoly_delineable_nonsep` → `{C, E, A2}`)
Mirror the proven separable case `separable_family_locally_delineable`: enumerate the distinct real
roots `t_j` of `g(0,0)` (`orderIsoOfFin`); per root, **simple** → analytic IFT (no axioms), **multiple**
→ translate `t ↦ t - t_j`, run `cluster_from_real` (C, E) for the complex sections, feed A2 for the real
functions; then glue (order, cover via degree count `∑ m_j = deg`, multiplicities). One enrichment
needed: expose `cluster_from_real`'s factorization (`u`, `hfac`, `u 0 ≠ 0`) so F3 can derive A2's
`hcover` (roots of `(fam y).map ℝ→ℂ` near the cluster `=` the `ψ_i`) from the `u`-unit relation.

**Remaining for the whole theorem (honest scope):**
- **Axiom hypothesis note:** proving `analytic_pseudopoly_delineable_nonsep` will need its `hP_elim` in
  the **analytic-cofactor** form (the `hPfull_elim_strong` shape, already constructed + soundness-checked
  at the call site `lifting_generalized_codim_local`) — a strengthening that does NOT weaken
  `mccallum_3_2_3_generalized` (the call site provides it). Likewise the cofactor degree bounds.
- **A2** the genuine nut: clustering *all* roots of `g(0,0)` into separated clusters near `0` with stable
  multiplicities, and supplying each cluster's `m` (root multiplicity) + translation to `t=0`.
- **F3** assembly across clusters: per-cluster `cluster_from_real` → `real_root_function` (F1) → order
  and glue into `analytic_pseudopoly_delineable_nonsep`.

**The entire per-cluster pipeline is complete** (Phase B, the whole D-phase descent, the complex
single-cluster pipeline, F1 per-section, all analyticity, **all of A3: frictions #1 product
reconciliation / #2 section-order / #3 factorization-differentiation, the membership bridge (b), the
C-axiom application (a), and the full real→complex closer `cluster_from_real`**). Everything from the
real per-cluster data to the complex root structure is proven, axiom-clean modulo only the named
classical axioms C and E. What remains is purely the **multi-cluster real-analysis assembly**: the A2
clustering nut (partition all roots of `g(0,0)` into separated stable clusters, supplying each `m`)
and the F3 glue (`cluster_from_real` + `real_root_function` per cluster → ordered real delineation
`analytic_pseudopoly_delineable_nonsep`) — plus the small `analyticOrderAt = rootMultiplicity` lemma.

### Connective chain — D3-APPLICATION PROVED (2026-05-30): `DiscOrder.lean` (option-1 validation)
New file `Mccalum/Generalized/DiscOrder.lean`, **sorry-free**, 0 custom axioms.
`weierstrassDisc_order_const_along_section` **wires the entire D-phase order machinery end-to-end**:
from the norm identity `P^m = weierstrassResFun·Q` (with analytic `Q`) + witness constant order
along the section, it produces exactly the `hdisc` hypothesis of `zariski_root_sections`
(`disc` has constant order along the section). The proof composes the built pieces:
`order_congr_of_eventuallyEq'` + `order_pow_analytic` + `order_factor_const_of_mul_analytic`
(the preconnected reverse bridge, with `S = {(y,0):y∈V}` the section image) + `order_weierstrassResFun_eq`.

Every hypothesis is a precise upstream obligation, so this lemma **validates the D-phase architecture
composes** and **pins down the exact interfaces** A/C/D1/D2 must deliver.

**KEY FINDING (option-1 payoff — the precise D1-input spec):** `norm_identity_elim` builds
`Q = Algebra.norm R (AdjoinRoot.mk h b)`, a polynomial in the Bézout cofactor `b`. So `Q` is analytic
**iff `b` is**. The D3-application genuinely *needs* `Q` analytic (the reverse bridge requires both
factors analytic). Therefore **D1-input must supply the membership `C(P) ∈ ⟨h,h'⟩` with *analytic*
cofactors — equivalently, over the analytic-germ ring `𝒪ₙ` (Phase B), not the pointwise function
ring.** This is exactly why `𝒪ₙ` is the right substrate (elements are analytic ⟹ `Q ∈ 𝒪ₙ` is
automatically analytic). The remaining D-phase plumbing: (i) analyticity of `weierstrassResFun`/
`weierstrassDiscFn` in the coefficients (resultant/disc are polynomials in the analytic `aᵢ`); (ii)
running `norm_identity_elim` over `𝒪ₙ` and transporting the germ identity to the `=ᶠ` function form
`hnorm`. Both are bounded; (ii) needs the germ↔function `resultant` identification (the germ half of
the eval infra).

## Bridge lemma (2026-05-29): `order_invariant_factor_of_mul` — PROVED, 0 custom axioms

In `DiscrProdInvariant.lean`. The **reverse** of `order_invariant_mul_mv`: if `f * g` is
order-invariant on a **connected** (not necessarily open) `S`, with `f, g ≠ 0`, then `f` and
`g` are each order-invariant on `S`. `#print axioms` → only `[propext, Classical.choice,
Quot.sound]`.

**Why it matters:** load-bearing step for removing the `non_null` hypothesis. Shows
`P` order-invariant on `S` ⟹ `disc(f)` order-invariant on `S` (via norm identity
`P^m = ±disc·Q`) with **no** non-vanishing assumption — exactly the case `non_null` papered
over (when `S ⊆ {disc=0}`, every admissible `P` vanishes on `S`).

**Method (no `non_null`, works on non-open `S`):** `polyOrder_ne_top_of_ne_zero` (finite order
for nonzero polys, via Taylor-shift + `MvPowerSeries.order_eq_top_iff`); `isClosed_polyOrder_ge`
(upper semicontinuity via continuous iterated Fréchet derivs); `polyOrder_factor_le`
(connectivity: `{f≤A}`,`{g<B}` open, cover `S`, disjoint on `S`); two USC functions summing to
a constant on a connected set are each constant.

**proof.tex gap found (codim case):** lines 441-444 / 466 silently assume `ord_0 P̃ < ⊤`
(restricted section order). False when `S ⊆ {disc=0}` (e.g. `f=(x₃-x₁)²-x₂`, `S={x₂=0}`: moving
double root, delineable, yet `disc̃ ≡ 0`). proof.tex's Zariski (Lifting.lean 1446-1448, "constant
**nonzero** order on ℂˢ") also excludes it. Honest fix: use the **ambient** order (constant along
`S` in ℝⁿ⁻¹), which `polyOrder`/`OrderInvariantMv` already measure. NOT an artifact of the
generalization — the discriminant itself vanishes on `S` in these cases (intrinsic to McCallum
Thm 2's codim case). **NEXT: axiom reformulation** to ambient (McCallum Thm 2) form, fed by this
bridge, dropping `non_null`.

## Order-transfer lemma (2026-05-29): `order_comp_eq_of_diffeo` — PROVED, 0 custom axioms

In `OrderComp.lean` (new file). **Vanishing `order` is invariant under a local analytic
diffeomorphism**: `order ℝ (g ∘ e) x = order ℝ g (e x)` for mutually-inverse smooth `e, e'`
on open sets. `#print axioms` → only `[propext, Classical.choice, Quot.sound]`.

**Method (no full Faà-di-Bruno):** one-directional `order_le_order_comp` via the *bound*
`norm_iteratedFDerivWithin_comp_le` with `C = 0` (all outer derivs vanish ⟹ composite deriv
norm ≤ 0 ⟹ zero); both directions + germ-invariance of order (`order_congr_of_eventuallyEq`)
give equality. Works locally on open sets (chart maps are only locally analytic).

**Role:** this is the gate for Option B (chosen path: keep minimal chart axiom, prove the
transfer). It lets `codim_local` feed the chart axiom the **full-chart** order of `P` (finite,
since `P ≠ 0`), which equals the ambient `polyOrder P` at the corresponding `S`-point — instead
of the chart-*restricted* order that is `⊤` exactly in the `disc|_section ≡ 0` cases. Combined
with `hP_oi` (ambient order-invariance), gives order-invariance of `P̃` along the section.

**Both Option-B gates now cleared** (bridge + transfer). REMAINING: restructure
`analytic_pseudopoly_delineable` to full-base (section × transverse) form taking the full order
along the section; rewire `codim_local` (g, P̃ over full chart; order hyps via transfer); drop
`non_null` through the chain + Projection.

## `non_null` REMOVED (2026-05-29) — theorem now = Rule 4.1 generalized

`mccallum_3_2_3_generalized` **no longer has** `hd_non_null`/`hr_non_null` (the discriminant/
resultant non-vanishing hypotheses). Its hypotheses now match Jasper's Rule 4.1 exactly
(an_sub, connected, non_null(f) [= `hnonzero`, f not nullified], `ord_inv(d)` [`hd_oi`],
`ord_inv(r)` [`hr_oi`], degree/coeff structure) — generalized to **arbitrary elimination-ideal
elements** `d, r`. `#print axioms` → `[analytic_pseudopoly_delineable, propext,
Classical.choice, Quot.sound]`. No sorries. Full project builds.

**How:** the axiom `analytic_pseudopoly_delineable` was restructured to the **full-base**
(section × transverse) form: it takes the family `g` and witness `P` over `ℝˢ × ℝⁿ⁻ˢ`, with
`P`'s order **finite at 0 and constant along the section** (the ambient order, finite even when
`disc|_section ≡ 0`), and concludes delineability over the section. `codim_local` feeds it via
`order_comp_partialHomeomorph_symm` (the chart transfer), so `order ℝ P̃ (y,0) = polyOrder P (Ψ y)`
= constant on `S` by `hP_oi` — no non-vanishing needed. The degree subtlety is sidestepped:
the axiom requires constant degree only **along the section** (true by leading-coeff continuity),
not off it.

**New supporting lemmas (both 0 custom axioms):**
- `order_invariant_factor_of_mul` (DiscrProdInvariant.lean) — reverse-order bridge (for the
  eventual axiom proof: `P` order-inv ⟹ `disc` order-inv).
- `order_comp_eq_of_diffeo`, `order_comp_partialHomeomorph_symm` (OrderComp.lean, new file) —
  vanishing order invariant under a local analytic diffeomorphism; load-bearing for feeding the axiom.

## Axiom decomposition — glue pieces being proven (2026-05-29)

Decomposing `analytic_pseudopoly_delineable` into named classical pieces. Status of the
documented decomposition steps:
- **Step 6 Schwarz reflection** — `real_restriction_analytic` (Lifting.lean): a function
  holomorphic at a real point restricts to a real-analytic function on `ℝˢ` (via
  `restrictScalars` + the `realEmbedding` CLM + `Re`). **PROVED, 0 custom axioms.**
- **Hypothesis-side glue, family complexification** — `complexify_pseudopoly` (Lifting.lean):
  a real pseudopolynomial family (analytic coeffs, degree ≤ N) complexifies to `gℂ : ℂᵐ → ℂ[t]`
  with analytic coeffs agreeing on the reals coefficient-wise. Built per-coefficient via
  `analyticAt_complexify` + reassembly with `Polynomial.monomial`. **PROVED, 0 custom axioms.**
  (Witness complexification = existing `analyticAt_complexify` directly. Remaining part-2 piece:
  the **membership** transfer `C P ∈ ⟨g,g'⟩ ⟹ C Pℂ ∈ ⟨gℂ,gℂ'⟩`, via complexifying the analytic
  witnesses + the identity theorem — fiddlier, deferred.)
- Bridge (`order_invariant_factor_of_mul`) and transfer (`order_comp_eq_of_diffeo`) — **PROVED**.
- **Remaining gaps (genuine, deep):** Weierstrass preparation (convergent) and Zariski root
  sections. A *correct* split needs `(base,t)`-analytic-germ-ring infrastructure — the
  Weierstrass factor `u` is a unit only in the germ ring, NOT in `ℝ[t]` (off the section it has
  `t`-roots). An `ℝ[t]`-level split would be a FALSE axiom; not pursued. The complex→real
  root-section *matching* (complex roots are unordered; must identify real-valued sections) is
  the other intricate remaining piece. These are scoped as dedicated future work.

So `non_null` is removed and the proven-glue for the eventual axiom elimination is accumulating
(bridge, transfer, Schwarz), but full axiom elimination remains a large analytic-geometry build.

## Axiom / sorry inventory

The main theorem chain depends on **1 axiom** + standard axioms. **No sorries.**

### Recently closed (2026-05-28): hPtilde_ne and hPtilde_oi
Inside `lifting_generalized_codim_local`, the two remaining sorries at the call site
of `analytic_pseudopoly_delineable` are now **PROVED**.

**API change:** Added hypothesis `hP_eval_p : MvPolynomial.eval p P ≠ 0` to
`lifting_generalized_codim_local`, propagated as `∀ a ∈ S, eval a P ≠ 0` through
`lifting_generalized_codim_case`, `lifting_theorem_generalized'`, and
`lifting_theorem_generalized`. At `mccallum_3_2_3_generalized`, added hypotheses
`hd_eval` and `hr_eval` (chosen elimination ideal elements don't vanish on S),
and derived `hP_eval` from them via the `elimProduct` factorization. This hypothesis
is natural for CAD: cells in a CAD decomposition are precisely the regions where
the chosen elimination ideal elements don't vanish.

### Axioms (in the chain)

**`analytic_pseudopoly_delineable`** (Lifting.lean) — sole remaining axiom.

This monolithic axiom bundles the deep complex-analytic core of the proof.
**Planned decomposition** (documented in the axiom's docstring):

1. **`weierstrass_preparation_complex`** (TODO axiom) — classical Weierstrass
   preparation theorem for holomorphic functions in several complex variables.
   Mathlib has the algebraic version (`PowerSeries.exists_isWeierstrassFactorization`);
   bridging to convergent power series is the gap.
2. **`zariski_root_sections_complex`** (TODO axiom) — Zariski's 1975 theorem on
   analytic root sections of a Weierstrass polynomial with disc of constant order.
3. **`real_root_section_of_complex`** (provable) — Schwarz reflection.
4. **`analytic_pseudopoly_delineable`** (would become a theorem proved from 1–3).

### Recently eliminated axiom (2026-05-28)

**`order_invariant_of_delineable`** — was an axiom, now **FULLY PROVED** (0 axioms).
Fix: changed `orderFull` definition from total multivariate order (`polyOrder`) to
`rootMultiplicity` of the specialized polynomial. With this definition, the theorem
follows trivially from delineability (constant rootMultiplicity on each section graph).

### Sorries: **NONE**

### Key definition change (2026-05-28)

`orderFull` (Invariance.lean) changed from:
```
polyOrder (n + 1) (toMvPoly f) (Fin.cons y a)
```
to:
```
if specialize f a = 0 then top else (specialize f a).rootMultiplicity y
```

The old definition used total multivariate order (via iterated Frechet derivatives).
This was wrong: a counterexample showed `order_invariant_of_delineable` was FALSE with
the old definition (f(x1,x2)(t) = t^2 + x1*x2, S = {x2=0}, theta = 0).

The new definition uses univariate rootMultiplicity of the specialized polynomial,
which is the correct notion for CAD lifting theorems.

### API changes (2026-05-28)
- `orderFull` definition changed (see above)
- `OrderInvariantFactor.lean` completely rewritten to use `rootMultiplicity`
- `order_invariant_full_factor_of_prod` gained `hspec` hypothesis:
  `forall f in A, forall p in T, specialize f p.1 != 0`
- `orderFull_eq_rootMultiplicity_at_delineable_root`: was sorry'd, now trivial 1-line proof
- `orderFull_eq_one_of_simple_root`: was complex polyOrder proof, now trivial 2-line proof

## Fully proved components

- `order_invariant_of_delineable` — delineability => order-invariance on sections, **PROVED**
- `order_mul_analytic` — order(fg) = order(f) + order(g), **PROVED**
- `order_additivity_holomorphic` — Thesis Lemma 4.1, **PROVED**
- `order_ne_top_of_ne_zero` — identity theorem (multi-variable), **PROVED**
- `isOpen_order_le_inter` — upper semi-continuity of order, **PROVED**
- `isOpen_order_lt_inter` — {order < b} open, **PROVED**
- `IsAnalyticSubmanifold.straightening_chart` — Theorem 2.2.1 (Submanifold.lean)
- `ift_local_root_section` — IFT for simple polynomial roots (SimpleRoots.lean)
- `separable_locally_delineable` — simple roots => local delineability (SimpleRoots.lean)
- `locally_delineable_to_global` — globalization, open case (SimpleRoots.lean)
- `locally_delineable_to_global'` — globalization, non-open connected sets (Lifting.lean)
- `order_invariant_of_locally_invariant` — globalization of order invariance (Lifting.lean)
- `lifting_generalized_open_case` — open case of lifting theorem (Lifting.lean)
- `lifting_generalized_codim_case` — codim case (Lifting.lean)
- `lifting_generalized_codim_local` — local codim case, **NO SORRIES** (Lifting.lean)
- `norm_eq_resultant_monic` — norm = resultant for monic polynomials (Lifting.lean)
- `norm_identity_elim` — P in elimination ideal => P^m = Res * Q (Lifting.lean)
- `norm_mk_mul_X_sub_C`, `norm_eq_prod_eval_of_monic_splits`,
  `norm_adjoinRoot_map` — supporting lemmas for norm chain (Lifting.lean)
- `exists_complement_of_surjective` — linear algebra helper (Submanifold.lean)
- `analyticAt_complexify` — real-analytic extends to holomorphic (Lifting.lean)
- `complexify_order_invariant` — constant order transfers to complexification (Lifting.lean)
- `hPtilde_elim` — Ptilde in <g, g'> proved via chart specialization (Lifting.lean)
- `orderFull_eq_rootMultiplicity_at_delineable_root` — trivial with new definition, **PROVED**
- `orderFull_eq_one_of_simple_root` — trivial with new definition, **PROVED**
- `isClosed_orderFull_ge` — superlevel sets of orderFull are closed, **PROVED**
- `order_invariant_full_factor_of_prod` — product OI => factor OI, **PROVED**

## Architecture

```
Projection.lean
  +-- mccallum_3_2_3_generalized  (Theorem 3.2.3')
        +-- lifting_theorem_generalized'  (Lifting.lean)
              |-- lifting_generalized_open_case  (s = r-1, S open)
              |     +-- simple_roots_delineable  (SimpleRoots.lean)
              |-- lifting_generalized_codim_case  (s < r-1, S submanifold)
              |     |-- lifting_generalized_codim_local  <- 0 sorries, 1 axiom
              |     |     +-- analytic_pseudopoly_delineable  (AXIOM)
              |     |-- order_invariant_of_delineable  (PROVED)
              |     |-- locally_delineable_to_global'
              |     +-- order_invariant_of_locally_invariant
              +-- norm_identity_elim
                    +-- norm_eq_resultant_monic
```

Last updated: 2026-05-28
