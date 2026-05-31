# Generalized McCallum Formalization — Status

## Main theorem
`mccallum_3_2_3_generalized` (Projection.lean) — proved from `lifting_theorem_generalized'`.
`non_null` removed; depends on **1 axiom** `analytic_pseudopoly_delineable` + standard. No sorries.

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
