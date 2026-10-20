module

public import FixedOrderFactor

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `FixedOrderFactor/`. The definitions used in the statements come
from `FixedOrderFactor/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

open Real Filter Topology

noncomputable section

namespace FixedOrderFactor

/-- **Local factor.** -/
theorem muAvg_eq {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) :=
  muAvg_eq' hr hx

/-- The full-circle factor is the limit of the order-`r` factor. -/
theorem tendsto_muAvg {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) :=
  tendsto_muAvg' hx

/-- **Random Euler product model, finite form.** -/
theorem modelMean_eq (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) :=
  modelMean_eq' r S

/-- **Correction factor as an Euler product.** -/
theorem hasProd_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) :=
  hasProd_correctionFactor' N hr

/-- **Model mean.** The product of the order-`r` local factors over the primes outside `N`. -/
theorem hasProd_muAvg (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) :=
  hasProd_muAvg' N hr

/-- The truncated model means converge to `ζ^{(N)}(2) · ζ^{(N)}(r)² / ζ^{(N)}(2r)`. -/
theorem tendsto_modelMean (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) :=
  tendsto_modelMean' N hr

/-- **Diagonal.** The pairs `(m, n) = (d a^r, d b^r)` with `a, b` coprime are what an average over
characters of order `r` keeps; their weights sum to the correction factor. -/
theorem hasSum_coprime_pairs (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (fun ab : ℕ × ℕ =>
        if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
        then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0)
      (correctionFactor N r) :=
  hasSum_coprime_pairs' N hr

/-- **Closed form for even order.** -/
theorem correctionFactor_even {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) :=
  correctionFactor_even' hk

/-- Removing finitely many Euler factors multiplies the correction factor by the local ratios. -/
theorem correctionFactor_eq_mul (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) :=
  correctionFactor_eq_mul' N hr

theorem one_lt_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r :=
  one_lt_correctionFactor' N hr

theorem correctionFactor_succ_lt (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r :=
  correctionFactor_succ_lt' N hr

theorem tendsto_correctionFactor (N : Finset Nat.Primes) :
    Tendsto (fun r => correctionFactor N r) atTop (𝓝 1) :=
  tendsto_correctionFactor' N

/-- **Quartic characters, factor at 2 removed: `35/34`.** -/
theorem correctionFactor_four_two : correctionFactor {two} 4 = 35 / 34 :=
  correctionFactor_four_two'

/-- The forced factor at `2`: `|1 ∓ i/2|⁻² = 4/5`. -/
theorem localTerm_I_half : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 :=
  localTerm_I_half'

/-- The constants of the quartic family. Two baselines are involved and are kept apart here.
`zetaN {two} 2 = π²/8` is the factor-removed full-family value (the limit in Louboutin's
Théorème 3, with the Euler factor at `2` removed); it is not stated in this theorem. The first
conjunct, `(4/5) · zetaN {two} 2 = π²/10`, is a different comparison value: the full-family
model with the factor at `2` reinserted as the single value `4/5 = |1 ∓ i/2|⁻²` that the
congruence `p ≡ 5 (mod 8)` forces for quartic characters. The second conjunct multiplies this by
the correction factor `35/34`, giving the order-four value `7π²/68` with the same forced factor.
The third is the naive random Euler product `ζ(2) · ζ(4)²/ζ(8) = 7π²/36`, with `χ(2)` uniform on
the fourth roots of unity. The last two conjuncts are the arithmetic relations
`7/136 = (1/20)(35/34) = (7/72)(9/17)` between the corresponding means of `h⁻/p`. -/
theorem quartic_constants :
    (4 / 5) * zetaN {two} 2 = π ^ 2 / 10 ∧
    (4 / 5) * zetaN {two} 2 * correctionFactor {two} 4 = 7 * π ^ 2 / 68 ∧
    zetaN ∅ 2 * correctionFactor ∅ 4 = 7 * π ^ 2 / 36 ∧
    (7 : ℝ) / 136 = 1 / 20 * (35 / 34) ∧ (7 : ℝ) / 136 = 7 / 72 * (9 / 17) :=
  quartic_constants'

end FixedOrderFactor
