module

public import FixedOrderFactor.Defs

@[expose] public section

open Real Filter Topology Complex Finset
namespace FixedOrderFactor

lemma rootOfUnity_eq (r j : ℕ) : rootOfUnity r j = Complex.exp (2 * π * I / r) ^ j := by
  rw [rootOfUnity, ← Complex.exp_nat_mul]; congr 1; ring

lemma rootOfUnity_pow_r {r : ℕ} (hr : 0 < r) (j : ℕ) : rootOfUnity r j ^ r = 1 := by
  rw [rootOfUnity_eq, ← pow_mul, mul_comm j r, pow_mul,
    (Complex.isPrimitiveRoot_exp r hr.ne').pow_eq_one, one_pow]

lemma sum_rootOfUnity_pow {r : ℕ} (hr : 0 < r) (m : ℕ) (hm : m < r) :
    ∑ j ∈ range r, rootOfUnity r j ^ m = if m = 0 then (r : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp r hr.ne'
  set ω := Complex.exp (2 * π * I / r)
  simp_rw [rootOfUnity_eq, ← pow_mul, mul_comm _ m, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ω ^ m ≠ 1 := hp.pow_ne_one_of_pos_of_lt h hm
    rw [geom_sum_eq hne, ← pow_mul, mul_comm m r, pow_mul, hp.pow_eq_one, one_pow, sub_self,
      zero_div]

lemma one_sub_mul_ne_zero {r : ℕ} (hr : 0 < r) (j : ℕ) {x : ℂ} (hx : x ^ r ≠ 1) :
    1 - rootOfUnity r j * x ≠ 0 := by
  intro h
  apply hx
  have h1 : rootOfUnity r j * x = 1 := by linear_combination -h
  have := congrArg (· ^ r) h1
  simpa [mul_pow, rootOfUnity_pow_r hr] using this

/-- `∑_{z^r = 1} 1/(1 - z x) = r/(1 - x^r)`. -/
lemma sum_inv_one_sub {r : ℕ} (hr : 0 < r) {x : ℂ} (hx : x ^ r ≠ 1) :
    ∑ j ∈ range r, 1 / (1 - rootOfUnity r j * x) = r / (1 - x ^ r) := by
  have hxr : 1 - x ^ r ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hterm : ∀ j ∈ range r, 1 / (1 - rootOfUnity r j * x) =
      (∑ m ∈ range r, rootOfUnity r j ^ m * x ^ m) / (1 - x ^ r) := by
    intro j _
    have hne := one_sub_mul_ne_zero hr j hx
    have ha : rootOfUnity r j * x ≠ 1 := fun h => hne (by rw [h, sub_self])
    simp_rw [← mul_pow]
    rw [geom_sum_eq ha, mul_pow, rootOfUnity_pow_r hr, one_mul]
    have : rootOfUnity r j * x - 1 ≠ 0 := sub_ne_zero.mpr ha
    field_simp
    ring
  rw [sum_congr rfl hterm, ← sum_div, sum_comm]
  simp_rw [← sum_mul]
  rw [sum_congr rfl (fun m hm => by rw [sum_rootOfUnity_pow hr m (mem_range.mp hm)])]
  rw [sum_eq_single 0]
  · simp
  · intro m _ hm; simp [hm]
  · intro h; exact absurd (mem_range.mpr hr) h

lemma conj_rootOfUnity (r j : ℕ) : (starRingEnd ℂ) (rootOfUnity r j) * rootOfUnity r j = 1 := by
  rw [rootOfUnity, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

lemma localTerm_complex (z : ℂ) (_hz : (starRingEnd ℂ) z * z = 1) (x : ℝ) :
    (localTerm z x : ℂ) = 1 / ((1 - z * x) * (1 - (starRingEnd ℂ) z * x)) := by
  rw [localTerm, Complex.ofReal_div, Complex.ofReal_one, ← Complex.mul_conj]
  simp [map_sub, Complex.conj_ofReal]

lemma partial_fraction {a b t : ℂ} (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hab : a * b = t)
    (ht : 1 - t ≠ 0) :
    1 / ((1 - a) * (1 - b)) = (1 / (1 - t)) * (1 / (1 - a) + 1 / (1 - b) - 1) := by
  subst hab
  field_simp
  ring

theorem muAvg_eq' {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) := by
  have hxr : |x| ^ r < 1 := pow_lt_one₀ (abs_nonneg x) hx hr.ne'
  have hxr' : x ^ r ≠ 1 := by
    intro h; rw [← abs_pow, h] at hxr; simp at hxr
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have : |x| ^ 2 = 1 := by rw [sq_abs, h]
    nlinarith [abs_nonneg x]
  have hxrC : (x : ℂ) ^ r ≠ 1 := by exact_mod_cast hxr'
  have h1 : (1 : ℝ) - x ^ r ≠ 0 := sub_ne_zero.mpr (Ne.symm hxr')
  have h2 : (1 : ℝ) - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx2)
  apply Complex.ofReal_injective
  have hsum1 := sum_inv_one_sub hr hxrC
  have hsum2 : ∑ j ∈ range r, 1 / (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) =
      r / (1 - (x : ℂ) ^ r) := by
    have := congrArg (starRingEnd ℂ) hsum1
    simpa [map_sum, map_div₀, map_sub, Complex.conj_ofReal] using this
  have hterm : ∀ j ∈ range r, (localTerm (rootOfUnity r j) x : ℂ) =
      (1 / (1 - (x : ℂ) ^ 2)) * (1 / (1 - rootOfUnity r j * x) +
        1 / (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) - 1) := by
    intro j _
    have hc := conj_rootOfUnity r j
    rw [localTerm_complex _ hc]
    have ha := one_sub_mul_ne_zero hr j hxrC
    have hb : 1 - (starRingEnd ℂ) (rootOfUnity r j) * x ≠ 0 := by
      intro h
      apply ha
      have h' : (starRingEnd ℂ) (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) = 0 := by
        rw [h, map_zero]
      simpa [map_sub, Complex.conj_ofReal] using h'
    exact partial_fraction ha hb (by linear_combination (x : ℂ) ^ 2 * hc) (by exact_mod_cast h2)
  rw [muAvg, Complex.ofReal_mul, Complex.ofReal_sum, sum_congr rfl hterm, ← mul_sum,
    sum_sub_distrib, sum_add_distrib, hsum1, hsum2]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1C : (1 : ℂ) - (x : ℂ) ^ r ≠ 0 := by exact_mod_cast h1
  have h2C : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h2
  push_cast
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring

end FixedOrderFactor
