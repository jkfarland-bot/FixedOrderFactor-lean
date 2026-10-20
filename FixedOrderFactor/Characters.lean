module

public import Mathlib

@[expose] public section

/-! # Orthogonality for the characters of order dividing `r` modulo a prime -/

open Finset

namespace FixedOrderFactor

variable (p : ℕ) [Fact p.Prime]

/-- The subgroup of `r`-th powers in `(ZMod p)ˣ`. -/
abbrev powers (r : ℕ) : Subgroup (ZMod p)ˣ := (powMonoidHom r : (ZMod p)ˣ →* (ZMod p)ˣ).range

/-- The characters trivial on the `r`-th powers. -/
noncomputable abbrev dualPowers (r : ℕ) : Subgroup (MulChar (ZMod p) ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ (powers p r)).ofDual

lemma mem_dualPowers_iff (r : ℕ) (χ : MulChar (ZMod p) ℂ) :
    χ ∈ dualPowers p r ↔ χ ^ r = 1 := by
  rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
  constructor
  · intro h
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val]
    exact h _ ⟨u, rfl⟩
  · rintro h _ ⟨u, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe, h,
      MulChar.one_apply_coe]

lemma card_dualPowers {r : ℕ} (hr : r ∣ p - 1) : Nat.card (dualPowers p r) = r := by
  rw [MulChar.card_subgroupOrderIsoSubgroupMulChar, ← Subgroup.index_eq_card,
    IsCyclic.index_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime Fact.out]
  exact Nat.gcd_eq_right hr

lemma symm_dualPowers (r : ℕ) :
    (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ).symm (OrderDual.toDual (dualPowers p r))
      = powers p r := by
  simp [dualPowers]

noncomputable instance (r : ℕ) : Fintype (dualPowers p r) := Fintype.ofFinite _

/-- Orthogonality over the characters trivial on the `r`-th powers. -/
lemma sum_dualPowers (r : ℕ) (u : (ZMod p)ˣ) :
    ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u =
      if u ∈ powers p r then (Nat.card (dualPowers p r) : ℂ) else 0 := by
  classical
  split_ifs with hu
  · have : ∀ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u = 1 := fun χ =>
      ((MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff).mp χ.2) u hu
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · have hne : ¬ ∀ χ ∈ dualPowers p r, χ u = 1 := by
      intro h; apply hu
      rw [← symm_dualPowers]
      exact MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff.mpr h
    push Not at hne
    obtain ⟨χ₀, hχ₀, h1⟩ := hne
    set S := ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u
    have hS : (χ₀ : MulChar (ZMod p) ℂ) u * S = S := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨χ₀, hχ₀⟩ : dualPowers p r)) _ _
        (fun χ => by simp [MulChar.coeToFun_mul])
    have : (χ₀ u - 1) * S = 0 := by linear_combination hS
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h

lemma mem_powers_iff (r : ℕ) (u : (ZMod p)ˣ) :
    u ∈ powers p r ↔ ∃ c : ZMod p, c ≠ 0 ∧ (u : ZMod p) = c ^ r := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.ne_zero, by simp⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨Units.mk0 c hc, ?_⟩
    ext; simp [h]

open Classical in
/-- **Orthogonality for characters of order dividing `r`.** For a prime `p` with `r ∣ p - 1`,
the sum of `χ(a) conj χ(b)` over the characters `χ` modulo `p` with `χʳ = 1` is `r` when
`a/b` is a nonzero `r`-th power modulo `p`, and `0` otherwise. -/
theorem sum_char_pow_eq_one' {r : ℕ} (hr : r ∣ p - 1) (a b : ZMod p) (hb : b ≠ 0) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ a * starRingEnd ℂ (χ b) =
      if ∃ c : ZMod p, c ≠ 0 ∧ a = c ^ r * b then (r : ℂ) else 0 := by
  have hterm : ∀ χ : DirichletCharacter ℂ p, χ a * starRingEnd ℂ (χ b) = χ (a * b⁻¹) := by
    intro χ
    rw [show starRingEnd ℂ (χ b) = star (χ b) from rfl, MulChar.star_apply',
      MulChar.inv_apply', map_mul]
  simp_rw [hterm]
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, MulChar.map_zero, Finset.sum_const_zero]
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro ⟨c, hc, h⟩
    exact mul_ne_zero (pow_ne_zero r hc) hb h.symm
  · set u : (ZMod p)ˣ := Units.mk0 (a * b⁻¹) (mul_ne_zero ha (inv_ne_zero hb))
    have hu : (u : ZMod p) = a * b⁻¹ := rfl
    rw [← hu]
    have hsum : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter
        (fun χ => χ ^ r = 1), χ u = ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u :=
      Finset.sum_subtype _ (fun χ => by
        rw [Finset.mem_filter, mem_dualPowers_iff]; simp) (fun χ : MulChar (ZMod p) ℂ => χ u)
    rw [hsum, sum_dualPowers, card_dualPowers p hr]
    congr 1
    rw [mem_powers_iff, hu]
    apply propext
    constructor
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [← h]; field_simp⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [h]; field_simp⟩

open Classical in
/-- There are exactly `r` characters modulo `p` with `χʳ = 1` when `r ∣ p - 1`. -/
theorem card_char_pow_eq_one' {r : ℕ} (hr : r ∣ p - 1) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1)).card = r := by
  trans Fintype.card (dualPowers p r)
  · rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => by
    rw [Finset.mem_filter, mem_dualPowers_iff]; simp))
  · rw [← Nat.card_eq_fintype_card, card_dualPowers p hr]

open Classical in
/-- If `m = d aʳ` and `n = d bʳ` and `p ∤ m n`, every character of order dividing `r` modulo `p`
has `χ(m) conj χ(n) = 1`, so these pairs survive the average over the family. -/
theorem sum_char_pow_eq_one_of_pow' {r : ℕ} (hr : r ∣ p - 1) {m n d a b : ℕ}
    (hm : m = d * a ^ r) (hn : n = d * b ^ r) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ m * starRingEnd ℂ (χ n) = r := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := (Fact.out : p.Prime).two_le
    rw [zero_dvd_iff] at hr; omega
  have hn0 : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [sum_char_pow_eq_one' p hr _ _ hn0, if_pos]
  have hd : (d : ZMod p) ≠ 0 := by
    intro h; apply hpn; rw [← ZMod.natCast_eq_zero_iff, hn]; push_cast; rw [h, zero_mul]
  have hb : (b : ZMod p) ≠ 0 := by
    intro h; apply hpn; rw [← ZMod.natCast_eq_zero_iff, hn]; push_cast; rw [h]
    simp [zero_pow hr0]
  have ha : (a : ZMod p) ≠ 0 := by
    intro h; apply hpm; rw [← ZMod.natCast_eq_zero_iff, hm]; push_cast; rw [h]
    simp [zero_pow hr0]
  refine ⟨(a : ZMod p) * (b : ZMod p)⁻¹, mul_ne_zero ha (inv_ne_zero hb), ?_⟩
  rw [hm, hn]; push_cast
  rw [mul_pow, inv_pow, mul_comm (d : ZMod p)]
  have hbr : ((b : ZMod p) ^ r)⁻¹ * (b : ZMod p) ^ r = 1 := inv_mul_cancel₀ (pow_ne_zero _ hb)
  rw [mul_assoc ((a : ZMod p) ^ r), ← mul_assoc ((b : ZMod p) ^ r)⁻¹, mul_comm _ (d : ZMod p),
    mul_right_comm ((b : ZMod p) ^ r)⁻¹, hbr, one_mul, mul_comm]

/-- The full family, for contrast: summed over all characters modulo `p`, `χ(m) conj χ(n)`
vanishes unless `m ≡ n (mod p)`; for `m ≠ n` below `p` it vanishes. -/
theorem sum_char_all' {m n : ℕ} (hmn : m ≠ n) (hm : m < p) (hn : n < p) (hn0 : n ≠ 0) :
    ∑ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) = 0 := by
  have hnu : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hn0 (Nat.eq_zero_of_dvd_of_lt h hn)
  have hterm : ∀ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) =
      χ ((n : ZMod p)⁻¹) * χ m := by
    intro χ
    rw [show starRingEnd ℂ (χ n) = star (χ n) from rfl, MulChar.star_apply',
      MulChar.inv_apply', mul_comm]
  simp_rw [hterm]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_iff_ne_zero.mpr hnu), if_neg]
  intro h
  apply hmn
  have := (ZMod.natCast_eq_natCast_iff' n m p).mp h
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact this.symm

end FixedOrderFactor
