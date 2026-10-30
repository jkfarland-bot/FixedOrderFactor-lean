# FixedOrderFactor

Lean 4 / Mathlib formalization accompanying J. S. Farland, *The factor 35/34: fourth powers in
the mean square of L(1, χ) over quartic characters* (preprint, Zenodo; all versions
[doi:10.5281/zenodo.23488965](https://doi.org/10.5281/zenodo.23488965); version 2 is
[doi:10.5281/zenodo.23491467](https://doi.org/10.5281/zenodo.23491467), and version 3 adds Section 7).

Archived on Zenodo: [doi:10.5281/zenodo.23489277](https://doi.org/10.5281/zenodo.23489277)
(all versions; release v1.0 is [doi:10.5281/zenodo.23489278](https://doi.org/10.5281/zenodo.23489278)).

Restricted to the odd quartic characters modulo primes `p ≡ 5 (mod 8)`, Louboutin's mean square of
`L(1, χ)` with the Euler factor at 2 removed has limit `(35/34)·π²/8` instead of `π²/8`. This
repository proves, inside the random Euler product model, where `35/34` comes from and its analogue
for characters of any order `r` with the Euler factors at any finite set `N` of primes removed:

- the order-`r` local factor `E_{z ∈ μ_r} |1 - z x|⁻² = (1 + xʳ)/((1 - x²)(1 - xʳ))`;
- `∏_{q ∉ N} (1 + q⁻ʳ)/(1 - q⁻ʳ) = ζ^(N)(r)² / ζ^(N)(2r)`, which is also `∑ (ab)⁻ʳ` over the
  coprime pairs prime to `N`;
- the model mean `ζ^(N)(2) ζ^(N)(r)² / ζ^(N)(2r)`;
- the factor exceeds 1, decreases strictly in `r` and tends to 1, and for `r = 2k` equals
  `-binom(4k, 2k) B_{2k}² / (2 B_{4k})` (with `N = ∅`);
- `r = 4`, `N = {2}` gives `35/34`, and the constants `π²/10`, `7π²/68`, `7π²/36` and
  `7/136 = (1/20)(35/34) = (7/72)(9/17)`.

Release v1.2 adds the finite part of how the limits are approached (Section 7 of version 3, from
Paper XI of the author's series). Under GRH and `L(1/2, ρ) ≠ 0`, for `b` odd, prime to `M` and not an
`r`-th power, in the family `p ≡ a (mod M)` the orbit average of `χ(b)` has bias `-β/√X` in
logarithmic mean, where `β` counts square roots:

- `β(M, a, s) = #{x ∈ (ℤ/M)ˣ : x² ≡ a (mod M), x ≡ -1 (mod s)}` (`sqrtCount`), with `s = s(b)` the
  order of the Kummer character of `b`;
- the orbit average `ϱ_s` on a Frobenius class satisfies `∑_{t<s} ϱ_s(ct) = s·[s ∣ c]`, so the
  class function has mean `0` and the sum giving the prime-square term is `s · β(M, a, s)`;
- `β` does not decrease as `s` decreases along divisibility; at `s = r` it is `0` unless `a` is a square in
  `H = ker((ℤ/M)ˣ → (ℤ/r)ˣ)`, and then it is the number of square roots of `1` in `H`;
- **imaginary families** (`r` even, `M = 2r`, `a = 1 + r`): `β = 0` for every `s` unless `8 ∣ r`,
  and `β = 0` for `s = r/d` with `d` odd. At `r = 4` this is `p ≡ 5 (mod 8)`, where no odd `b` has a
  leading bias;
- the predicted counts of Paper XI's table, checked by `decide`.

The passage from the model to the primes (the actual limit over `p`) and the bias theorem itself are
not formalized; they need the prime ideal theorem over `ℚ(ζ_r)`, Chebotarev, Kummer theory and the
explicit formula under GRH, which Mathlib does not have.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (releases v1.0 and v1.1 used `v4.35.0-rc2`).

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface a reader should audit. It restates the definitions
  exactly as the development has them and states the twenty-nine results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `FixedOrderFactor/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the
  [Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate).

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

Section numbers refer to version 3 of the paper (Sections 1 to 6 are numbered as in version 2).

| Paper | Challenge declaration |
|---|---|
| Theorem 2.1 (local factor) | `muAvg_eq`, `tendsto_muAvg` |
| Theorem 3.1 (Euler product) | `hasProd_correctionFactor`, `hasProd_muAvg` |
| Theorem 3.2 (diagonal) | `hasSum_coprime_pairs` |
| Proposition 3.3 (surviving pairs) | `div_eq_pow_iff`, `model_pair_average` |
| Theorem 3.4 (model) | `modelMean_eq`, `tendsto_modelMean` |
| Theorem 3.5 (shape) | `correctionFactor_eq_mul`, `one_lt_correctionFactor`, `correctionFactor_succ_lt`, `tendsto_correctionFactor` |
| Proposition 3.6 (even order) | `correctionFactor_even` |
| **Theorem 4.1 (35/34 and the quartic constants)** | `correctionFactor_four_two`, `localTerm_I_half`, `quartic_constants` |
| Theorem 5.1 (orthogonality, one prime) | `card_char_pow_eq_one`, `sum_char_pow_eq_one` |
| Corollary 5.2 | `sum_char_pow_eq_one_of_pow`, `sum_char_all` |
| Proposition 7.3 (square-root count) | `sum_orbitAvg_mul`, `sum_orbitAvg_eq_zero`, `sum_orbitAvg_square` |
| Corollary 7.4 (class criterion) | `sqrtCount_le_of_dvd`, `sqrtCount_top`, `sqrtCount_top_dichotomy` |
| **Corollary 7.5 (imaginary families)** | `sqrtCount_imaginary` |
| Table 2 | `sqrtCount_table` |

## Files

| File | Contents |
|---|---|
| `Defs.lean` | `PrimeTo`, `zetaN`, `correctionFactor`, `rootOfUnity`, `localTerm`, `muAvg`, `modelMean`, `primesUpTo`, `two`, `sqrtCount`, `orbitAvg` |
| `Euler.lean` | Euler product for `zetaN` over the primes outside `N`; the correction factor as a product |
| `Local.lean` | the average over the `r`-th roots of unity |
| `Model.lean` | the finite random model and its limit |
| `Order.lean` | dependence on `N`, `> 1`, strictly decreasing in `r`, limit `1` |
| `Values.lean` | Bernoulli closed form, `B₈ = -1/30`, `35/34` and the quartic constants |
| `Diagonal.lean` | the sum over coprime pairs, by regrouping pairs by their gcd |
| `Pairs.lean` | `m/n` is an `r`-th power in `ℚ` iff `(m, n) = (d aʳ, d bʳ)` |
| `ModelPairs.lean` | the model average `E[z^m conj(z^n)]` |
| `Characters.lean` | orthogonality for the characters with `χʳ = 1` modulo a prime |
| `Bias.lean` | square-root counts: the orbit average, the prime-square term, the class criterion, imaginary families |
