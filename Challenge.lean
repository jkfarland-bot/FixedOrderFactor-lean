module

public import Mathlib

public section

/-!
# The order-`r` correction factor for mean squares of `L(1, χ)`

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each headline result with
`sorry`. `Solution.lean` proves every statement below with the same name and type, using the
development in `FixedOrderFactor/`.

Throughout, `r` is a natural number and `N` a finite set of primes, and
`ζ^{(N)}(s) = ζ(s) ∏_{q ∈ N} (1 - q⁻ˢ)` is written `zetaN N s`.

## Results

* `muAvg_eq`: the average of `|1 - z x|⁻²` over the `r`-th roots of unity is
  `(1 + xʳ)/((1 - x²)(1 - xʳ))`; `tendsto_muAvg`: as `r → ∞` it tends to the full-circle
  value `(1 - x²)⁻¹`.
* `modelMean_eq`, `hasProd_muAvg`, `tendsto_modelMean`: the random Euler product model for
  characters of order `r` has mean `ζ^{(N)}(2) ζ^{(N)}(r)² / ζ^{(N)}(2r)` over the primes
  outside `N`.
* `hasProd_correctionFactor`: `∏_{q ∉ N} (1 + q⁻ʳ)/(1 - q⁻ʳ) = ζ^{(N)}(r)² / ζ^{(N)}(2r)`.
* `hasSum_coprime_pairs`: the same factor is `∑ (ab)⁻ʳ` over coprime pairs prime to `N`.
* `correctionFactor_even`: for even `r = 2k`,
  `ζ(2k)²/ζ(4k) = -binom(4k, 2k) B_{2k}² / (2 B_{4k})`.
* `correctionFactor_eq_mul`, `one_lt_correctionFactor`, `correctionFactor_succ_lt`,
  `tendsto_correctionFactor`: dependence on `N`, and the factor exceeds `1`, decreases strictly
  in `r`, and tends to `1`.
* `correctionFactor_four_two`, `localTerm_I_half`, `quartic_constants`: for quartic characters
  with the factor at `2` removed the correction is `35/34`, and the constants
  `π²/10`, `7π²/68`, `7π²/36` and `7/136 = (1/20)(35/34) = (7/72)(9/17)`.
-/

open Real Filter Topology

noncomputable section

namespace FixedOrderFactor

/-- `n` is divisible by no prime of `N`. -/
def PrimeTo (N : Finset Nat.Primes) (n : ℕ) : Prop := ∀ q ∈ N, ¬ (q : ℕ) ∣ n

instance instDecidablePrimeTo (N : Finset Nat.Primes) : DecidablePred (PrimeTo N) :=
  fun n => inferInstanceAs (Decidable (∀ q ∈ N, ¬ (q : ℕ) ∣ n))

/-- `ζ(s)` with the Euler factors at the primes of `N` removed, as a series over `n ≥ 1`. -/
def zetaN (N : Finset Nat.Primes) (s : ℕ) : ℝ :=
  ∑' n : ℕ, if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0

/-- The correction factor `ζ^{(N)}(r)² / ζ^{(N)}(2r)`. -/
def correctionFactor (N : Finset Nat.Primes) (r : ℕ) : ℝ :=
  zetaN N r ^ 2 / zetaN N (2 * r)

/-- The `j`-th power of the standard primitive `r`-th root of unity. -/
def rootOfUnity (r j : ℕ) : ℂ := Complex.exp (2 * π * Complex.I * j / r)

/-- The local factor `|1 - z x|⁻²`. -/
def localTerm (z : ℂ) (x : ℝ) : ℝ := 1 / Complex.normSq (1 - z * x)

/-- The average of `|1 - z x|⁻²` over the `r`-th roots of unity `z`. -/
def muAvg (r : ℕ) (x : ℝ) : ℝ := (1 / r) * ∑ j ∈ Finset.range r, localTerm (rootOfUnity r j) x

/-- The truncated random model: the average, over independent choices of an `r`-th root of unity
`z_q` at each prime `q ∈ S`, of `∏_{q ∈ S} |1 - z_q/q|⁻²`. -/
def modelMean (r : ℕ) (S : Finset Nat.Primes) : ℝ :=
  (1 / (r : ℝ) ^ S.card) * ∑ z : S → Fin r,
    ∏ q : S, localTerm (rootOfUnity r (z q)) (1 / ((q : Nat.Primes) : ℝ))

/-- The primes `q ≤ Y` outside `N`. -/
def primesUpTo (N : Finset Nat.Primes) (Y : ℕ) : Finset Nat.Primes :=
  ((Finset.range (Y + 1)).preimage (fun q : Nat.Primes => (q : ℕ))
    Nat.Primes.coe_nat_injective.injOn).filter (· ∉ N)

/-- The prime `2` as an element of `Nat.Primes`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- **Local factor.** -/
theorem muAvg_eq {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) := sorry

/-- The full-circle factor is the limit of the order-`r` factor. -/
theorem tendsto_muAvg {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) := sorry

/-- **Random Euler product model, finite form.** -/
theorem modelMean_eq (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) := sorry

/-- **Correction factor as an Euler product.** -/
theorem hasProd_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) := sorry

/-- **Model mean.** The product of the order-`r` local factors over the primes outside `N`. -/
theorem hasProd_muAvg (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) := sorry

/-- The truncated model means converge to `ζ^{(N)}(2) · ζ^{(N)}(r)² / ζ^{(N)}(2r)`. -/
theorem tendsto_modelMean (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) := sorry

/-- **Diagonal.** The pairs `(m, n) = (d a^r, d b^r)` with `a, b` coprime are what an average over
characters of order `r` keeps; their weights sum to the correction factor. -/
theorem hasSum_coprime_pairs (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (fun ab : ℕ × ℕ =>
        if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
        then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0)
      (correctionFactor N r) := sorry

/-- **Closed form for even order.** -/
theorem correctionFactor_even {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) := sorry

/-- Removing finitely many Euler factors multiplies the correction factor by the local ratios. -/
theorem correctionFactor_eq_mul (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) := sorry

theorem one_lt_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r := sorry

theorem correctionFactor_succ_lt (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r := sorry

theorem tendsto_correctionFactor (N : Finset Nat.Primes) :
    Tendsto (fun r => correctionFactor N r) atTop (𝓝 1) := sorry

/-- **Quartic characters, factor at 2 removed: `35/34`.** -/
theorem correctionFactor_four_two : correctionFactor {two} 4 = 35 / 34 := sorry

/-- The forced factor at `2`: `|1 ∓ i/2|⁻² = 4/5`. -/
theorem localTerm_I_half : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 := sorry

/-- The constants of the quartic family: Louboutin's full-family value `π²/10`, the order-four
value `7π²/68`, and the relation `7/136 = (1/20)(35/34) = (7/72)(9/17)`. -/
theorem quartic_constants :
    (4 / 5) * zetaN {two} 2 = π ^ 2 / 10 ∧
    (4 / 5) * zetaN {two} 2 * correctionFactor {two} 4 = 7 * π ^ 2 / 68 ∧
    zetaN ∅ 2 * correctionFactor ∅ 4 = 7 * π ^ 2 / 36 ∧
    (7 : ℝ) / 136 = 1 / 20 * (35 / 34) ∧ (7 : ℝ) / 136 = 7 / 72 * (9 / 17) := sorry

end FixedOrderFactor
