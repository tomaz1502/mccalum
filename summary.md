  1. Assertion 1 → Lifting Theorem (3.2.1'): Proved. locally_delineable_to_global patches local delineability on a connected set
  into global delineability. The overall lifting_theorem_generalized' assembles the result.
  2. Assertion 2 → Assertion 1: Proved. separable_locally_delineable — at each point, the IFT (ift_local_root_section, now fully
  proved) gives a local analytic root section for each simple root, then these are combined to establish local delineability with
  the right multiplicities.
  3. Case s = r − 1 of Assertion 2: Proved. lifting_generalized_open_case — since S is open, P is order-invariant and nonzero on a
   connected open set, so P is nowhere-vanishing. Then P ∈ ⟨f, f'⟩ with P(p) ≠ 0 forces all roots of f(p, ·) to be simple. The IFT
   applies directly.

  What remains unproved is the case 1 ≤ s ≤ r − 2 (Section 6.3 in your thesis) — the positive codimension case. That's
  lifting_generalized_codim_case, the sole remaining axiom. It requires coordinate changes, complexification, Weierstrass
  preparation, the elimination ideal factorization P̃ = disc(h) · Q (Corollary 5.2), the order additivity lemma (Lemma 4.1), and
  Zariski's theorem.
