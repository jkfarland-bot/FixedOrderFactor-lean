module

public import FixedOrderFactor.Euler
public import FixedOrderFactor.Local

@[expose] public section

open Real Filter Topology Finset
namespace FixedOrderFactor

theorem tendsto_muAvg' {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
  have hx2 : (1 : ℝ) - x ^ 2 ≠ 0 := by
    have : x ^ 2 < 1 := by
      have := sq_abs x; nlinarith [abs_nonneg x]
    linarith
  have hlim : Tendsto (fun r : ℕ => (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r))) atTop
      (𝓝 ((1 + 0) / ((1 - x ^ 2) * (1 - 0)))) := by
    refine ((tendsto_const_nhds.add hp)).div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)) ?_
    simpa using hx2
  simp only [add_zero, sub_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  exact (muAvg_eq' hr hx).symm

theorem modelMean_eq' (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) := by
  unfold modelMean muAvg
  rw [← Finset.prod_coe_sort S (fun q => (1 / (r : ℝ)) * ∑ j ∈ range r,
      localTerm (rootOfUnity r j) (1 / (q : ℝ)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  congr 1
  · rw [one_div_pow]
  · simp_rw [← Fin.sum_univ_eq_sum_range (fun j => localTerm (rootOfUnity r j) _) r]
    exact (Fintype.prod_sum (fun (q : S) (j : Fin r) =>
      localTerm (rootOfUnity r j) (1 / ((q : Nat.Primes) : ℝ)))).symm

lemma abs_inv_q_lt_one (q : Nat.Primes) : |1 / (q : ℝ)| < 1 := by
  rw [abs_of_pos (inv_q_pos q)]; exact inv_q_lt_one q

theorem hasProd_muAvg' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) := by
  have := (hasProd_zetaN N le_rfl).mul (hasProd_correctionFactor' N hr)
  convert this using 1
  funext q
  rw [muAvg_eq' (by omega) (abs_inv_q_lt_one q.1)]
  have h1 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ r ≠ 0 :=
    sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
  have h2 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
  field_simp

/-- The primes `q ≤ Y` outside `N`, as a finset of the subtype. -/
noncomputable def primesUpTo' (N : Finset Nat.Primes) (Y : ℕ) : Finset {q : Nat.Primes // q ∉ N} :=
  (primesUpTo N Y).subtype (· ∉ N)

lemma mem_primesUpTo (N : Finset Nat.Primes) (Y : ℕ) (q : Nat.Primes) :
    q ∈ primesUpTo N Y ↔ (q : ℕ) ≤ Y ∧ q ∉ N := by
  rw [primesUpTo, Finset.mem_filter]
  have : q ∈ (Finset.range (Y + 1)).preimage (fun q : Nat.Primes => (q : ℕ))
      Nat.Primes.coe_nat_injective.injOn ↔ (q : ℕ) ∈ Finset.range (Y + 1) :=
    Finset.mem_preimage
  rw [this, Finset.mem_range]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩

theorem tendsto_modelMean' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) := by
  have hT : Tendsto (primesUpTo' N) atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro Y Z hYZ q hq
      simp only [primesUpTo', mem_subtype, mem_primesUpTo] at hq ⊢
      exact ⟨hq.1.trans hYZ, hq.2⟩
    · intro q
      refine ⟨q.1, ?_⟩
      simp only [primesUpTo', mem_subtype, mem_primesUpTo]
      exact ⟨le_rfl, q.2⟩
  have h := (hasProd_muAvg' N hr).comp hT
  refine h.congr (fun Y => ?_)
  simp only [Function.comp_apply]
  rw [modelMean_eq']
  unfold primesUpTo'
  refine (Finset.prod_subtype_eq_prod_filter (s := primesUpTo N Y) (p := (· ∉ N))
    (f := fun p : Nat.Primes => muAvg r (1 / (p : ℝ)))).trans ?_
  rw [Finset.filter_true_of_mem]
  intro q hq
  exact ((mem_primesUpTo N Y q).mp hq).2

end FixedOrderFactor
