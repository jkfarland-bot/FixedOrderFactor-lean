# FixedOrderFactor

Lean 4 / Mathlib formalization accompanying J. S. Farland, *The factor 35/34: fourth powers in
the mean square of L(1, χ) over quartic characters* (preprint,
[doi:10.5281/zenodo.23488966](https://doi.org/10.5281/zenodo.23488966)).

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

The passage from the model to the primes (the actual limit over `p`) is not formalized; it needs the
prime ideal theorem over `ℚ(ζ_r)`, which Mathlib does not have.

Toolchain: `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface a reader should audit. It restates the definitions
  exactly as the development has them and states the fifteen results with `sorry`.
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

| Paper | Challenge declaration |
|---|---|
| Theorem 2.1 (local factor) | `muAvg_eq`, `tendsto_muAvg` |
| Theorem 3.1 (Euler product) | `hasProd_correctionFactor`, `hasProd_muAvg` |
| Theorem 3.2 (diagonal) | `hasSum_coprime_pairs` |
| Theorem 3.3 (model) | `modelMean_eq`, `tendsto_modelMean` |
| Theorem 3.4 (shape) | `correctionFactor_eq_mul`, `one_lt_correctionFactor`, `correctionFactor_succ_lt`, `tendsto_correctionFactor` |
| Proposition 3.5 (even order) | `correctionFactor_even` |
| **Theorem 4.1 (35/34 and the quartic constants)** | `correctionFactor_four_two`, `localTerm_I_half`, `quartic_constants` |

## Files

| File | Contents |
|---|---|
| `Defs.lean` | `PrimeTo`, `zetaN`, `correctionFactor`, `rootOfUnity`, `localTerm`, `muAvg`, `modelMean`, `primesUpTo`, `two` |
| `Euler.lean` | Euler product for `zetaN` over the primes outside `N`; the correction factor as a product |
| `Local.lean` | the average over the `r`-th roots of unity |
| `Model.lean` | the finite random model and its limit |
| `Order.lean` | dependence on `N`, `> 1`, strictly decreasing in `r`, limit `1` |
| `Values.lean` | Bernoulli closed form, `B₈ = -1/30`, `35/34` and the quartic constants |
| `Diagonal.lean` | the sum over coprime pairs, by regrouping pairs by their gcd |
