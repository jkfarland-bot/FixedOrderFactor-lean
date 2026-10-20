module

public import Mathlib

@[expose] public section

/-! # The pairs whose ratio is an `r`-th power -/

namespace FixedOrderFactor

/-- **The surviving pairs.** For positive integers `m, n`, the quotient `m/n` is the `r`-th power
of a rational number exactly when `m = d aʳ` and `n = d bʳ` with `a, b` coprime. -/
theorem div_eq_pow_iff' {r m n : ℕ} (hr : 0 < r) (hm : 0 < m) (hn : 0 < n) :
    (∃ q : ℚ, (m : ℚ) / n = q ^ r) ↔
      ∃ d a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ m = d * a ^ r ∧ n = d * b ^ r := by
  constructor
  · rintro ⟨q, hq⟩
    have hpos : (0 : ℚ) < (m : ℚ) / n := by positivity
    have hq' : (m : ℚ) / n = |q| ^ r := by
      rw [← abs_pow, ← hq, abs_of_pos hpos]
    set a := q.num.natAbs
    set b := q.den
    have hab : Nat.Coprime a b := q.reduced
    have hqa : |q| = (a : ℚ) / b := by
      rw [Rat.abs_def]
      simp [a, b, Rat.divInt_eq_div]
    have hb : 0 < b := q.den_pos
    have hq0 : q ≠ 0 := by
      rintro rfl; rw [abs_zero, zero_pow hr.ne'] at hq'; exact hpos.ne' hq'
    have ha : 0 < a := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq0)
    -- `m bʳ = n aʳ`
    have hmn : m * b ^ r = n * a ^ r := by
      rw [hqa, div_pow, div_eq_div_iff (by positivity) (by positivity)] at hq'
      rw [mul_comm (n : ℕ)]; exact_mod_cast hq'
    have hcop : Nat.Coprime (a ^ r) (b ^ r) := Nat.Coprime.pow r r hab
    have hdvd : a ^ r ∣ m := by
      have : a ^ r ∣ m * b ^ r := ⟨n, by rw [hmn, mul_comm]⟩
      exact hcop.dvd_of_dvd_mul_right this
    obtain ⟨d, hd⟩ := hdvd
    refine ⟨d, a, b, ha, hb, hab, by rw [hd, mul_comm], ?_⟩
    have hapos : 0 < a ^ r := pow_pos ha r
    rw [hd] at hmn
    have : n * a ^ r = d * b ^ r * a ^ r := by rw [← hmn]; ring
    exact Nat.eq_of_mul_eq_mul_right hapos this
  · rintro ⟨d, a, b, ha, hb, -, rfl, rfl⟩
    refine ⟨(a : ℚ) / b, ?_⟩
    have hd : d ≠ 0 := by rintro rfl; simp at hm
    push_cast
    rw [div_pow]
    field_simp

end FixedOrderFactor
