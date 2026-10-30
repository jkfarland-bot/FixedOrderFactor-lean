module

/-
  The order-`r` correction factor: definitions.
  Formalization accompanying J. S. Farland, "The order-r correction factor for mean squares of
  L(1, χ)" (2026).
-/

public import Mathlib

@[expose] public section

/-!
# Definitions

Throughout, `r` is a natural number and `N` is a finite set of primes.

* `PrimeTo N n`: no prime of `N` divides `n`.
* `zetaN N s = ζ^{(N)}(s) = ∑_{n ≥ 1, (n, N) = 1} n⁻ˢ`, which is `ζ(s) ∏_{q ∈ N} (1 - q⁻ˢ)`.
* `correctionFactor N r = ζ^{(N)}(r)² / ζ^{(N)}(2r)`.
* `rootOfUnity r j = e^{2πij/r}`, `localTerm z x = |1 - z x|⁻²`, and `muAvg r x` is the
  average of `localTerm z x` over the `r`-th roots of unity `z`.
* `modelMean r S` is the mean of the truncated random Euler product
  `∏_{q ∈ S} |1 - z_q/q|⁻²` over independent uniform `r`-th roots of unity `z_q`.
* `primesUpTo N Y` is the set of primes `q ≤ Y` not in `N`, and `two` is the prime `2`.
* `sqrtCount M a s` is the square-root count `β(M, a, s)` of the Chebyshev bias, and
  `orbitAvg s t` is the average of `e^{2πiut/s}` over the units `u` modulo `s`.
-/

open Real

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

/-- The square-root count `β(M, a, s)`: the number of units `x` modulo `M` with `x² ≡ a (mod M)`
and `x ≡ -1 (mod s)`, counted over the representatives `0 ≤ x < M`. -/
def sqrtCount (M a s : ℕ) : ℕ :=
  ((Finset.range M).filter fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M ∧ s ∣ x + 1).card

/-- The orbit average `ϱ_s(t) = φ(s)⁻¹ ∑_{u ∈ (ℤ/s)ˣ} e^{2πi ut/s}` of a character of order `s`
evaluated at an element whose `s`-th power residue symbol is `e^{2πit/s}`. -/
def orbitAvg (s t : ℕ) : ℂ :=
  (1 / (s.totient : ℂ)) * ∑ u ∈ (Finset.range s).filter s.Coprime, rootOfUnity s (u * t)

end FixedOrderFactor
