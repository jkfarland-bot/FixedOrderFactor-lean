module

public import FixedOrderFactor.Model

@[expose] public section

open Real Filter Topology Finset
namespace FixedOrderFactor

lemma le_of_hasProd_one_le {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a : ℝ} (h : HasProd f a)
    (hf : ∀ i, 1 ≤ f i) (i₀ : ι) : f i₀ ≤ a := by
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop {i₀}] with s hs
  have hi : i₀ ∈ s := hs (mem_singleton_self i₀)
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : 1 ≤ ∏ i ∈ s.erase i₀, f i := one_le_prod₀ (fun i _ => hf i)
  nlinarith [hf i₀]

lemma hasProd_le_of_le_one {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a : ℝ} (h : HasProd f a)
    (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ 1) (i₀ : ι) : a ≤ f i₀ := by
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop {i₀}] with s hs
  have hi : i₀ ∈ s := hs (mem_singleton_self i₀)
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : ∏ i ∈ s.erase i₀, f i ≤ 1 := prod_le_one₀ (fun i _ => hf0 i) (fun i _ => hf i)
  have h0 : 0 ≤ ∏ i ∈ s.erase i₀, f i := prod_nonneg (fun i _ => hf0 i)
  nlinarith [hf0 i₀]

lemma exists_prime_not_mem (N : Finset Nat.Primes) : ∃ q : Nat.Primes, q ∉ N := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes ((N.sup (fun q => (q : ℕ))) + 1)
  refine ⟨⟨p, hp2⟩, fun h => ?_⟩
  have := Finset.le_sup (f := fun q : Nat.Primes => (q : ℕ)) h
  simp at this; omega

/-- The Euler factor `(1 + y)/(1 - y)`. -/
lemma factor_gt_one {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 1 < (1 + y) / (1 - y) := by
  rw [lt_div_iff₀ (by linarith)]; linarith

theorem one_lt_correctionFactor' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_prime_not_mem N
  have h := hasProd_correctionFactor' N hr
  have hf : ∀ q : {q : Nat.Primes // q ∉ N}, 1 < (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r) :=
    fun q => factor_gt_one (pow_pos (inv_q_pos q.1) r) (pow_inv_q_lt_one q.1 (by omega))
  exact lt_of_lt_of_le (hf ⟨q₀, hq₀⟩) (le_of_hasProd_one_le h (fun q => (hf q).le) ⟨q₀, hq₀⟩)

lemma correctionFactor_pos (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    0 < correctionFactor N r := lt_trans one_pos (one_lt_correctionFactor' N hr)

theorem correctionFactor_succ_lt' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_prime_not_mem N
  have hA := hasProd_correctionFactor' N (by omega : 2 ≤ r + 1)
  have hB := (hasProd_correctionFactor' N hr).inv₀ (correctionFactor_pos N hr).ne'
  have h := hA.mul hB
  set g : {q : Nat.Primes // q ∉ N} → ℝ := fun q =>
    (1 + (1 / (q : ℝ)) ^ (r + 1)) / (1 - (1 / (q : ℝ)) ^ (r + 1)) *
      ((1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))⁻¹
  have hg : ∀ q, 0 < g q ∧ g q < 1 := by
    intro q
    set x := 1 / ((q : Nat.Primes) : ℝ)
    have hx0 : 0 < x := inv_q_pos q.1
    have hx1 : x < 1 := inv_q_lt_one q.1
    have hy0 : 0 < x ^ r := pow_pos hx0 r
    have hy1 : x ^ r < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
    have hyy : x ^ (r + 1) < x ^ r := pow_lt_pow_right_of_lt_one₀ hx0 hx1 (by omega)
    have hz0 : 0 < x ^ (r + 1) := pow_pos hx0 _
    have hz1 : x ^ (r + 1) < 1 := lt_trans hyy hy1
    have hd1 : 0 < 1 - x ^ r := by linarith
    have hd2 : 0 < 1 - x ^ (r + 1) := by linarith
    constructor
    · show 0 < (1 + x ^ (r + 1)) / (1 - x ^ (r + 1)) * ((1 + x ^ r) / (1 - x ^ r))⁻¹
      positivity
    · show (1 + x ^ (r + 1)) / (1 - x ^ (r + 1)) * ((1 + x ^ r) / (1 - x ^ r))⁻¹ < 1
      rw [inv_div, div_mul_div_comm, div_lt_one (by positivity)]
      nlinarith
  have hle := hasProd_le_of_le_one h (fun q => (hg q).1.le) (fun q => (hg q).2.le) ⟨q₀, hq₀⟩
  have hlt := lt_of_le_of_lt hle (hg ⟨q₀, hq₀⟩).2
  have hpos := correctionFactor_pos N hr
  rwa [← div_eq_mul_inv, div_lt_one hpos] at hlt

theorem correctionFactor_eq_mul' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) := by
  have hterm : ∀ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) =
      (1 - (1 / (q : ℝ)) ^ r) ^ 2 / (1 - (1 / (q : ℝ)) ^ (2 * r)) := by
    intro q _
    have h0 : 0 < (1 / (q : ℝ)) ^ r := pow_pos (inv_q_pos q) r
    have h1 : (1 / (q : ℝ)) ^ r < 1 := pow_inv_q_lt_one q (by omega)
    rw [pow_mul', sq]
    have : (1 : ℝ) - (1 / (q : ℝ)) ^ r * (1 / (q : ℝ)) ^ r =
        (1 - (1 / (q : ℝ)) ^ r) * (1 + (1 / (q : ℝ)) ^ r) := by ring
    rw [show ((1 / (q : ℝ)) ^ r) ^ 2 = (1 / (q : ℝ)) ^ r * (1 / (q : ℝ)) ^ r by ring, this]
    have h2 : (1 : ℝ) - (1 / (q : ℝ)) ^ r ≠ 0 := by linarith
    have h3 : (1 : ℝ) + (1 / (q : ℝ)) ^ r ≠ 0 := by linarith
    field_simp
  rw [prod_congr rfl hterm, prod_div_distrib, prod_pow]
  unfold correctionFactor
  rw [zetaN_eq N hr, zetaN_eq N (by omega : 2 ≤ 2 * r)]
  have hP : (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ (2 * r))) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun q _ => sub_ne_zero.mpr (pow_inv_q_lt_one q (by omega)).ne')
  have hZ : zetaN ∅ (2 * r) ≠ 0 := (zetaN_pos ∅ (by omega)).ne'
  field_simp

lemma zetaN_empty_le (s : ℕ) (hs : 2 ≤ s) :
    zetaN ∅ s ≤ 1 + (1 / 2) ^ (s - 2) * zetaN ∅ 2 := by
  have hsum2 := summable_zetaN_terms ∅ (le_refl 2)
  have hsums := summable_zetaN_terms ∅ hs
  have hite : Summable (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {1}) (fun n hn => by simp at hn; simp [hn])
  have hle : ∀ n : ℕ, (if 0 < n ∧ PrimeTo ∅ n then 1 / (n : ℝ) ^ s else 0) ≤
      (if n = 1 then 1 else 0) +
        (1 / 2) ^ (s - 2) * (if 0 < n ∧ PrimeTo ∅ n then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n
    have hP : PrimeTo ∅ n := fun q hq => absurd hq (Finset.notMem_empty q)
    rcases Nat.lt_trichotomy n 1 with h | h | h
    · have : n = 0 := by omega
      subst this; simp
    · subst h; simp [hP]
    · have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
      simp only [show 0 < n by omega, hP, and_self, if_true, show n ≠ 1 by omega, if_false,
        zero_add]
      have hpos : (0 : ℝ) < n := by linarith
      rw [show s = (s - 2) + 2 by omega, pow_add]
      simp only [show s - 2 + 2 - 2 = s - 2 by omega]
      rw [← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← one_div_pow]
      exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) hn) _
  have := Summable.tsum_le_tsum hle hsums (hite.add (hsum2.mul_left _))
  rw [Summable.tsum_add hite (hsum2.mul_left _), tsum_mul_left, tsum_ite_eq] at this
  exact this

lemma tendsto_zetaN_empty : Tendsto (fun s => zetaN ∅ s) atTop (𝓝 1) := by
  have hc : Tendsto (fun s : ℕ => 1 + (1 / 2 : ℝ) ^ (s - 2) * zetaN ∅ 2) atTop (𝓝 1) := by
    have h0 : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ (s - 2)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat 2)
    simpa using tendsto_const_nhds.add (h0.mul_const (zetaN ∅ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with s hs using one_le_zetaN ∅ hs
  · filter_upwards [eventually_ge_atTop 2] with s hs using zetaN_empty_le s hs

theorem tendsto_correctionFactor' (N : Finset Nat.Primes) :
    Tendsto (fun r => correctionFactor N r) atTop (𝓝 1) := by
  have h1 : Tendsto (fun r => correctionFactor ∅ r) atTop (𝓝 1) := by
    have hA := tendsto_zetaN_empty
    have hB := tendsto_zetaN_empty.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have := (hA.pow 2).div hB one_ne_zero
    simp only [one_pow, div_one] at this
    exact this
  have h2 : Tendsto (fun r : ℕ => ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r))
      atTop (𝓝 1) := by
    have : ∀ q ∈ N, Tendsto (fun r : ℕ => (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r))
        atTop (𝓝 1) := by
      intro q _
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_q_pos q).le (inv_q_lt_one q)
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hp |>.div
        ((tendsto_const_nhds (x := (1 : ℝ))).add hp) (by norm_num)
      simp only [sub_zero, add_zero, div_one] at this
      exact this
    simpa using tendsto_finset_prod N this
  have := h1.mul h2
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with r hr
  exact (correctionFactor_eq_mul' N hr).symm

end FixedOrderFactor
