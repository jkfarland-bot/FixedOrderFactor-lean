module

public import FixedOrderFactor.Defs

@[expose] public section

open Real Filter Topology
namespace FixedOrderFactor

lemma primeTo_one (N : Finset Nat.Primes) : PrimeTo N 1 := by
  intro q _ h; exact q.prop.one_lt.ne' (Nat.dvd_one.mp h)

lemma primeTo_mul_iff (N : Finset Nat.Primes) (m n : ℕ) :
    PrimeTo N (m * n) ↔ PrimeTo N m ∧ PrimeTo N n := by
  unfold PrimeTo
  constructor
  · intro h; exact ⟨fun q hq hm => h q hq (hm.mul_right n), fun q hq hn => h q hq (hn.mul_left m)⟩
  · rintro ⟨hm, hn⟩ q hq hmn
    rcases (Nat.Prime.dvd_mul q.prop).mp hmn with h | h
    exacts [hm q hq h, hn q hq h]

/-- The completely multiplicative function `n ↦ 1_{PrimeTo N}(n) n⁻ˢ`. -/
noncomputable def fN (N : Finset Nat.Primes) (s : ℕ) (hs : s ≠ 0) : ℕ →*₀ ℝ where
  toFun n := if PrimeTo N n then 1 / (n : ℝ) ^ s else 0
  map_zero' := by simp [hs]
  map_one' := by simp [primeTo_one]
  map_mul' m n := by
    simp only [primeTo_mul_iff, Nat.cast_mul, mul_pow]
    by_cases hm : PrimeTo N m <;> by_cases hn : PrimeTo N n <;> simp [hm, hn, one_div, mul_comm]

lemma fN_apply (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) (n : ℕ) :
    fN N s hs n = if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0 := by
  show (if PrimeTo N n then 1 / (n : ℝ) ^ s else 0) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs]
  · simp [hn]

lemma summable_fN (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖fN N s (by omega) n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))
  rw [fN_apply]; split_ifs <;> simp

lemma zetaN_eq_tsum_fN (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) :
    zetaN N s = ∑' n, fN N s hs n := by
  simp only [zetaN, fN_apply]

/-- Euler product for `zetaN`, over the primes outside `N`. -/
theorem hasProd_zetaN (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => (1 - (1 / (q : ℝ)) ^ s)⁻¹) (zetaN N s) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_fN N hs)
  rw [← zetaN_eq_tsum_fN] at h
  have hsupp : Function.mulSupport (fun p : Nat.Primes => (1 - fN N s (by omega) p)⁻¹) ⊆
      {q | q ∉ N} := by
    intro q hq
    simp only [Set.mem_ofPred_eq]
    intro hqN
    apply hq
    show (1 - (if PrimeTo N q then 1 / ((q : ℕ) : ℝ) ^ s else 0))⁻¹ = 1
    rw [if_neg (fun h => h q hqN dvd_rfl)]; simp
  have h2 : HasProd (fun q : {q : Nat.Primes // q ∉ N} => (1 - fN N s (by omega) q.1)⁻¹)
      (zetaN N s) := (hasProd_subtype_iff_of_mulSupport_subset hsupp).mpr h
  convert h2 using 1
  funext q
  show _ = (1 - (if PrimeTo N q.1 then 1 / ((q.1 : ℕ) : ℝ) ^ s else 0))⁻¹
  rw [if_pos]
  · simp [one_div, inv_pow]
  · intro p hp hdvd
    have := (Nat.prime_dvd_prime_iff_eq p.prop q.1.prop).mp hdvd
    exact q.2 (by rwa [← Subtype.ext this])


lemma summable_zetaN_terms (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0) := by
  exact (summable_fN N hs).of_norm.congr (fun n => fN_apply N _ n)

lemma one_le_zetaN (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) : 1 ≤ zetaN N s := by
  have h := (summable_zetaN_terms N hs).le_tsum 1 (fun n _ => by split_ifs <;> positivity)
  simpa [primeTo_one, zetaN] using h

lemma zetaN_pos (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) : 0 < zetaN N s :=
  lt_of_lt_of_le one_pos (one_le_zetaN N hs)

lemma inv_q_pos (q : Nat.Primes) : 0 < 1 / (q : ℝ) := by
  have := q.prop.pos; positivity

lemma inv_q_le_half (q : Nat.Primes) : 1 / (q : ℝ) ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast q.prop.two_le
  exact one_div_le_one_div_of_le (by norm_num) this

lemma inv_q_lt_one (q : Nat.Primes) : 1 / (q : ℝ) < 1 :=
  lt_of_le_of_lt (inv_q_le_half q) (by norm_num)

lemma pow_inv_q_lt_one (q : Nat.Primes) {s : ℕ} (hs : s ≠ 0) : (1 / (q : ℝ)) ^ s < 1 :=
  pow_lt_one₀ (inv_q_pos q).le (inv_q_lt_one q) hs

/-- Euler product for `zetaN`, over all primes, with the factors at `N` equal to `1`. -/
theorem zetaN_eq_mul_prod (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN ∅ s = (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s)⁻¹) * zetaN N s := by
  set g : Nat.Primes → ℝ := fun q => (1 - (1 / (q : ℝ)) ^ s)⁻¹
  have hall : HasProd g (zetaN ∅ s) := by
    have h := hasProd_zetaN ∅ hs
    have hsupp : Function.mulSupport g ⊆ {q | q ∉ (∅ : Finset Nat.Primes)} := by
      intro q _; simp
    exact (hasProd_subtype_iff_of_mulSupport_subset hsupp).mp h
  have hN : HasProd (g ∘ (↑) : (↑(N : Set Nat.Primes) : Type) → ℝ) (∏ q ∈ N, g q) := by
    have := hasProd_fintype (g ∘ ((↑) : (↑(N : Set Nat.Primes) : Type) → Nat.Primes))
    convert this using 1
    exact (Finset.prod_coe_sort N g).symm.trans (by rfl)
  have hc : HasProd (g ∘ (↑) : (↑((N : Set Nat.Primes)ᶜ) : Type) → ℝ) (zetaN N s) :=
    hasProd_zetaN N hs
  exact hall.unique (hN.mul_isCompl isCompl_compl hc)

theorem zetaN_eq (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN N s = zetaN ∅ s * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s) := by
  have hprod : (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s)⁻¹) * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun q _ => inv_mul_cancel₀ (sub_ne_zero.mpr
      (pow_inv_q_lt_one q (by omega)).ne'))
  rw [zetaN_eq_mul_prod N hs]
  linear_combination (-zetaN N s) * hprod

theorem hasProd_correctionFactor' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) := by
  have hA := hasProd_zetaN N hr
  have hB := (hasProd_zetaN N (by omega : 2 ≤ 2 * r)).inv₀ (zetaN_pos N (by omega)).ne'
  have := (hA.mul hA).mul hB
  unfold correctionFactor
  convert this using 1
  · funext q
    have h1 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ r ≠ 0 :=
      sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
    simp only [inv_inv, pow_mul]
    field_simp
    ring
  · rw [div_eq_mul_inv, sq]

end FixedOrderFactor
