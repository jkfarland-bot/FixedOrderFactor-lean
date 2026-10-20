module

public import FixedOrderFactor.Order

@[expose] public section

open Real Filter Topology Finset
namespace FixedOrderFactor
lemma b5 : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, Nat.choose]
  norm_num
lemma b6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, Nat.choose]
  norm_num
lemma b7 : bernoulli' 7 = 0 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, b6, Nat.choose]
  norm_num
lemma b8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, b6, b7, Nat.choose]
  norm_num

lemma zetaN_empty_eq {s : ℕ} (hs : s ≠ 0) : zetaN ∅ s = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  unfold zetaN
  congr 1; funext n
  have hP : PrimeTo ∅ n := fun q hq => absurd hq (Finset.notMem_empty q)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs]
  · simp [hn, hP]

lemma zetaN_empty_two_mul {k : ℕ} (hk : k ≠ 0) :
    zetaN ∅ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
  rw [zetaN_empty_eq (by omega), (hasSum_zeta_nat hk).tsum_eq]

theorem correctionFactor_even' {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) := by
  have hZ := zetaN_pos ∅ (by omega : 2 ≤ 2 * (2 * k))
  unfold correctionFactor
  rw [show 2 * (2 * k) = 2 * (2 * k) from rfl] at hZ ⊢
  rw [zetaN_empty_two_mul hk.ne', zetaN_empty_two_mul (by omega : 2 * k ≠ 0)] at *
  rw [show 2 * (2 * k) = 4 * k by ring] at *
  have hB : (bernoulli (4 * k) : ℝ) ≠ 0 := by
    intro h; rw [h] at hZ; simp at hZ
  have hch : ((4 * k).factorial : ℝ) =
      (Nat.choose (4 * k) (2 * k) : ℝ) * (2 * k).factorial * (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * k ≤ 4 * k)
    rw [show 4 * k - 2 * k = 2 * k by omega] at this
    exact_mod_cast this.symm
  have h2 : (2 : ℝ) ^ (4 * k - 1) = 2 * ((2 : ℝ) ^ (2 * k - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_succ']; congr 1; omega
  have hm1 : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  have hm2 : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpi : (π ^ (2 * k)) ^ 2 = π ^ (4 * k) := by rw [← pow_mul]; ring_nf
  rw [hch, h2, hm1, div_pow, mul_pow, mul_pow, mul_pow, hm2, hpi]
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hp : π ^ (4 * k) ≠ 0 := by positivity
  have h2' : ((2 : ℝ) ^ (2 * k - 1)) ≠ 0 := by positivity
  field_simp

lemma bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

lemma bernoulli_eight' : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), b8]

lemma correctionFactor_empty_four : correctionFactor ∅ 4 = 7 / 6 := by
  have := correctionFactor_even' (k := 2) (by norm_num)
  norm_num [bernoulli_four', bernoulli_eight', Nat.choose] at this
  rw [this]

theorem correctionFactor_four_two' : correctionFactor {two} 4 = 35 / 34 := by
  rw [correctionFactor_eq_mul' _ (by norm_num), correctionFactor_empty_four,
    Finset.prod_singleton]
  simp [two]; norm_num

theorem localTerm_I_half' : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 := by
  constructor <;> · simp [localTerm, Complex.normSq_apply]; norm_num

lemma zetaN_empty_two : zetaN ∅ 2 = π ^ 2 / 6 := by
  rw [zetaN_empty_eq (by norm_num), hasSum_zeta_two.tsum_eq]

lemma zetaN_two_two : zetaN {two} 2 = π ^ 2 / 8 := by
  rw [zetaN_eq _ (le_refl 2), zetaN_empty_two, Finset.prod_singleton]
  simp [two]; ring

theorem quartic_constants' :
    (4 / 5) * zetaN {two} 2 = π ^ 2 / 10 ∧
    (4 / 5) * zetaN {two} 2 * correctionFactor {two} 4 = 7 * π ^ 2 / 68 ∧
    zetaN ∅ 2 * correctionFactor ∅ 4 = 7 * π ^ 2 / 36 ∧
    (7 : ℝ) / 136 = 1 / 20 * (35 / 34) ∧ (7 : ℝ) / 136 = 7 / 72 * (9 / 17) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [zetaN_two_two]; ring
  · rw [zetaN_two_two, correctionFactor_four_two']; ring
  · rw [zetaN_empty_two, correctionFactor_empty_four]; ring

end FixedOrderFactor
