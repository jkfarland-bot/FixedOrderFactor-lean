module

public import FixedOrderFactor.Defs
public import FixedOrderFactor.Pairs

@[expose] public section

/-! # The random model keeps exactly the `r`-th power ratios -/

open Finset Complex

namespace FixedOrderFactor

/-- `ω = e^{2πi/r}`. -/
noncomputable abbrev ω (r : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / r)

lemma omega_pow_r {r : ℕ} (hr : 0 < r) : ω r ^ r = 1 :=
  (Complex.isPrimitiveRoot_exp r hr.ne').pow_eq_one

lemma omega_ne_zero (r : ℕ) : ω r ≠ 0 := Complex.exp_ne_zero _

lemma conj_omega (r : ℕ) : starRingEnd ℂ (ω r) = (ω r)⁻¹ := by
  rw [ω, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

lemma rootOfUnity_eq_omega (r j : ℕ) : rootOfUnity r j = ω r ^ j := by
  rw [rootOfUnity, ω, ← Complex.exp_nat_mul]; congr 1; ring

/-- `∑_{k<r} ω^{ke} = r` if `r ∣ e`, and `0` otherwise. -/
lemma sum_omega_zpow {r : ℕ} (hr : 0 < r) (e : ℤ) :
    ∑ k : Fin r, ω r ^ ((k : ℤ) * e) = if (r : ℤ) ∣ e then (r : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp r hr.ne'
  have h1 : ∀ k : Fin r, ω r ^ ((k : ℤ) * e) = (ω r ^ e) ^ (k : ℕ) := by
    intro k; rw [← zpow_natCast, ← zpow_mul, mul_comm]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ω r ^ e) ^ k) r]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    rw [zpow_mul, zpow_natCast, omega_pow_r hr, one_zpow]
    simp
  · have hne : ω r ^ e ≠ 1 := by
      intro h; exact hd ((hp.zpow_eq_one_iff_dvd e).mp h)
    rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      omega_pow_r hr, one_zpow, sub_self, zero_div]

/-- `∏_{q ∈ S} q^{v_q(m)} = m` when every prime factor of `m` lies in `S`. -/
lemma prod_pow_factorization_eq {S : Finset Nat.Primes} {m : ℕ} (hm : 0 < m)
    (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m → q ∈ S) :
    ∏ q ∈ S, ((q : ℕ) : ℚ) ^ (m.factorization q) = m := by
  have hinj : Function.Injective (fun q : Nat.Primes => (q : ℕ)) := Nat.Primes.coe_nat_injective
  have e : ∏ q ∈ S, ((q : ℕ) : ℚ) ^ (m.factorization q) =
      ∏ p ∈ S.map ⟨_, hinj⟩, (p : ℚ) ^ m.factorization p :=
    (Finset.prod_map S ⟨_, hinj⟩ (fun p : ℕ => (p : ℚ) ^ m.factorization p)).symm
  rw [e]
  have hsub : m.primeFactors ⊆ S.map ⟨_, hinj⟩ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_map]
    exact ⟨⟨p, hpp⟩, hS ⟨p, hpp⟩ (Nat.dvd_of_mem_primeFactors hp), rfl⟩
  rw [← Finset.prod_subset hsub]
  · have := Nat.prod_factorization_pow_eq_self hm.ne'
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact_mod_cast this
  · intro p hpS hp
    have hpp : p.Prime := by
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hpS
      exact q.2
    rw [Nat.factorization_eq_zero_of_not_dvd, pow_zero]
    intro hdvd
    exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hm.ne'⟩)

/-- `m/n` is an `r`-th power in `ℚ` exactly when `r` divides every `v_q(m) - v_q(n)`. -/
lemma pow_iff_dvd_valuations {r : ℕ} (hr : 0 < r) {S : Finset Nat.Primes} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (∃ x : ℚ, (m : ℚ) / n = x ^ r) ↔
      ∀ q ∈ S, (r : ℤ) ∣ (m.factorization q : ℤ) - n.factorization q := by
  constructor
  · intro h q _
    obtain ⟨d, a, b, ha, hb, -, rfl, rfl⟩ := (div_eq_pow_iff' hr hm hn).mp h
    have hd : d ≠ 0 := by rintro rfl; simp at hm
    rw [Nat.factorization_mul hd (pow_ne_zero _ ha.ne'),
      Nat.factorization_mul hd (pow_ne_zero _ hb.ne'), Nat.factorization_pow,
      Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨(a.factorization q : ℤ) - b.factorization q, by push_cast; ring⟩
  · intro h
    refine ⟨∏ q ∈ S, ((q : ℕ) : ℚ) ^
      (((m.factorization q : ℤ) - n.factorization q) / r), ?_⟩
    rw [← Finset.prod_pow]
    have hq : ∀ q ∈ S, (((q : ℕ) : ℚ) ^ (((m.factorization q : ℤ) - n.factorization q) / r)) ^ r
        = ((q : ℕ) : ℚ) ^ (m.factorization q) / ((q : ℕ) : ℚ) ^ (n.factorization q) := by
      intro q hqS
      have hq0 : ((q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.2.ne_zero
      rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (h q hqS), zpow_sub₀ hq0,
        zpow_natCast, zpow_natCast]
    rw [Finset.prod_congr rfl hq, Finset.prod_div_distrib,
      prod_pow_factorization_eq hm (fun q hq => hS q (hq.mul_right n)),
      prod_pow_factorization_eq hn (fun q hq => hS q (hq.mul_left m))]

/-- For a choice `j : S → Fin r` of `r`-th roots of unity `z_q = e^{2πi j_q/r}` at the primes of
`S`, the value `z^m = ∏_{q ∈ S} z_q^{v_q(m)}`. -/
noncomputable def zPow (r : ℕ) (S : Finset Nat.Primes) (j : S → Fin r) (m : ℕ) : ℂ :=
  ∏ q : S, rootOfUnity r ((j q : ℕ) * m.factorization (q : Nat.Primes))

lemma zPow_mul_conj (r : ℕ) (S : Finset Nat.Primes) (j : S → Fin r) (m n : ℕ) :
    zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      ∏ q : S, ω r ^ (((j q : ℕ) : ℤ) *
        ((m.factorization (q : Nat.Primes) : ℤ) - n.factorization (q : Nat.Primes))) := by
  unfold zPow
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [rootOfUnity_eq_omega, rootOfUnity_eq_omega, map_pow, conj_omega, inv_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (omega_ne_zero r)]
  congr 1
  push_cast; ring

open Classical in
/-- **The model keeps exactly the `r`-th power ratios.** If `z_q` are independent and uniform on
the `r`-th roots of unity, then `E[z^m conj(z^n)]` is `1` when `m/n` is the `r`-th power of a
rational number and `0` otherwise (for `m, n ≥ 1` whose prime factors lie in `S`). -/
theorem model_pair_average' {r : ℕ} (hr : 0 < r) (S : Finset Nat.Primes) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (1 / (r : ℂ) ^ S.card) * ∑ j : S → Fin r, zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      if ∃ x : ℚ, (m : ℚ) / n = x ^ r then 1 else 0 := by
  simp_rw [zPow_mul_conj]
  rw [← Fintype.prod_sum (fun (q : S) (k : Fin r) => ω r ^ (((k : ℕ) : ℤ) *
      ((m.factorization (q : Nat.Primes) : ℤ) - n.factorization (q : Nat.Primes))))]
  simp_rw [sum_omega_zpow hr]
  rw [pow_iff_dvd_valuations hr hm hn hS]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  split_ifs with h
  · rw [Finset.prod_congr rfl (fun q _ => if_pos (h q.1 q.2)), Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]
    field_simp
  · push Not at h
    obtain ⟨q, hqS, hq⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ ⟨q, hqS⟩) (if_neg hq), mul_zero]

end FixedOrderFactor
