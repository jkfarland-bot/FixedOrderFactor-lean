module

public import FixedOrderFactor.Local

@[expose] public section

/-!
# Square-root counts for the Chebyshev bias

Let `r ∣ M`, `a ≡ 1 (mod r)`, and consider the primes `p ≡ a (mod M)`. For `b` with `s = s(b)`
(the order of the Kummer character of `b` on the family), the bias of the orbit average of `χ(b)`
is `-β/√X` with the square-root count

  `β(M, a, s) = #{x ∈ (ℤ/M)ˣ : x² ≡ a (mod M), x ≡ -1 (mod s)}`   (`sqrtCount M a s`).

The analytic input (the explicit formula under GRH) is not formalized. What is formalized is the
finite computation that produces `β` and the arithmetic of `β`:

* `sum_rootOfUnity_mul`, `sum_orbitAvg_mul`: `∑_{t<s} ϱ_s(ct) = s·[s ∣ c]`, where
  `ϱ_s(t) = φ(s)⁻¹ ∑_{u ∈ (ℤ/s)ˣ} e^{2πiut/s}` is the orbit average on the Frobenius class.
* `sum_orbitAvg_eq_zero`: the class function has mean zero, `∑_{t<s} ϱ_s(t) = 0` for `s > 1`.
* `sum_orbitAvg_square`: the prime-square term. The squares `(t, x)² = ((1 + x)t, x²)` of the
  elements of `ℤ/s ⋊ (ℤ/M)ˣ` give `∑_{x² = a} ∑_{t<s} ϱ_s((x + 1)t) = s · β(M, a, s)`.
* `sqrtCount_le_of_dvd`: `β` is nondecreasing as `s` decreases along divisibility.
* `sqrtCount_eq_card_zmod`, `sqrtCount_top`, `sqrtCount_top_dichotomy`: at `s = r`,
  `x ↦ -x` identifies the count with the square roots of `a` in `H = ker((ℤ/M)ˣ → (ℤ/r)ˣ)`, and
  this is `0` unless `a` is a square in `H`, when it equals the number of square roots of `1`.
* `sqrtCount_imaginary`: for even `r`, `M = 2r` and `a = 1 + r` (the imaginary families),
  `β = 0` for every `s` unless `8 ∣ r`, and `β = 0` whenever `s = r/d` with `d` odd.
-/

open Finset Real Complex

namespace FixedOrderFactor

/-- `∑_{t<s} e^{2πict/s}` is `s` if `s ∣ c` and `0` otherwise. -/
lemma sum_rootOfUnity_mul {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, rootOfUnity s (c * t) = if s ∣ c then (s : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp s hs.ne'
  set ω := Complex.exp (2 * π * I / s)
  have h : ∀ t, rootOfUnity s (c * t) = (ω ^ c) ^ t := fun t => by
    rw [rootOfUnity_eq, ← pow_mul]
  simp_rw [h]
  by_cases hc : s ∣ c
  · have h1 : ω ^ c = 1 := (hp.pow_eq_one_iff_dvd c).2 hc
    simp [h1, hc]
  · have hne : ω ^ c ≠ 1 := fun h1 => hc ((hp.pow_eq_one_iff_dvd c).1 h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm c s, pow_mul, hp.pow_eq_one, one_pow, sub_self,
      zero_div, ite_eq_right_iff.2 (fun h => absurd h hc)]

/-- `∑_{t<s} ϱ_s(ct) = s` if `s ∣ c` and `0` otherwise. -/
theorem sum_orbitAvg_mul' {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, orbitAvg s (c * t) = if s ∣ c then (s : ℂ) else 0 := by
  unfold orbitAvg
  rw [← mul_sum, sum_comm]
  have hu : ∀ u ∈ (range s).filter s.Coprime,
      ∑ t ∈ range s, rootOfUnity s (u * (c * t)) = if s ∣ c then (s : ℂ) else 0 := by
    intro u hu
    have hcop : s.Coprime u := (mem_filter.1 hu).2
    simp_rw [show ∀ t, u * (c * t) = (u * c) * t from fun t => by ring]
    rw [sum_rootOfUnity_mul hs]
    by_cases hc : s ∣ c
    · rw [ite_eq_left_iff.2 (fun h => absurd (dvd_mul_of_dvd_right hc u) h),
        ite_eq_left_iff.2 (fun h => absurd hc h)]
    · have hn : ¬ s ∣ u * c := fun h => hc (hcop.dvd_of_dvd_mul_left h)
      rw [ite_eq_right_iff.2 (fun h => absurd h hn), ite_eq_right_iff.2 (fun h => absurd h hc)]
  rw [sum_congr rfl hu, sum_const, nsmul_eq_mul]
  have hcard : ((range s).filter s.Coprime).card = s.totient := (Nat.totient_eq_card_coprime s).symm
  rw [hcard]
  have : (s.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hs).ne'
  field_simp

/-- The class function has mean zero: `∑_{t<s} ϱ_s(t) = 0` for `s > 1`. -/
theorem sum_orbitAvg_eq_zero' {s : ℕ} (hs : 1 < s) : ∑ t ∈ range s, orbitAvg s t = 0 := by
  have h := sum_orbitAvg_mul' (s := s) (by omega) 1
  simp only [one_mul] at h
  rw [h, ite_eq_right_iff.2]
  intro hd
  have := Nat.le_of_dvd one_pos hd
  omega

/-- **The prime-square term.** With `(t, x)² = ((1 + x)t, x²)` in `ℤ/s ⋊ (ℤ/M)ˣ`,
`∑_{x² ≡ a} ∑_{t<s} ϱ_s((x + 1)t) = s · β(M, a, s)`. -/
theorem sum_orbitAvg_square' {s : ℕ} (hs : 0 < s) (M a : ℕ) :
    ∑ x ∈ (range M).filter (fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M),
      ∑ t ∈ range s, orbitAvg s ((x + 1) * t) = s * sqrtCount M a s := by
  simp_rw [sum_orbitAvg_mul' hs]
  rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter, mul_comm]
  simp only [sqrtCount, and_assoc]

/-- `β` is nondecreasing as `s` decreases along divisibility. -/
theorem sqrtCount_le_of_dvd' (M a : ℕ) {s s' : ℕ} (h : s' ∣ s) :
    sqrtCount M a s ≤ sqrtCount M a s' := by
  unfold sqrtCount
  apply card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1, h.trans hx.2.2.2⟩

section ZModForm

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
lemma castHom_natCast_eq_neg_one_iff {s : ℕ} (hs : s ∣ M) (x : ℕ) :
    ZMod.castHom hs (ZMod s) (x : ZMod M) = -1 ↔ s ∣ x + 1 := by
  rw [map_natCast, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one,
    eq_neg_iff_add_eq_zero]

/-- With `s ∣ M`, `β(M, a, s)` counts the units `y` of `ℤ/M` with `y² = a` and `y ≡ -1 (mod s)`. -/
theorem sqrtCount_eq_card_zmod {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    sqrtCount M a s = (univ.filter fun y : ZMod M =>
      IsUnit y ∧ y ^ 2 = a ∧ ZMod.castHom hs (ZMod s) y = -1).card := by
  unfold sqrtCount
  refine card_nbij' (fun x => (x : ZMod M)) (fun y => y.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨(ZMod.isUnit_iff_coprime x M).2 hx.2.1, ?_, (castHom_natCast_eq_neg_one_iff hs x).2 hx.2.2.2⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
    exact hx.2.2.1
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    have hy' : ((y.val : ℕ) : ZMod M) = y := ZMod.natCast_zmod_val y
    refine ⟨ZMod.val_lt y, (ZMod.isUnit_iff_coprime _ M).1 (by rw [hy']; exact hy.1), ?_,
      (castHom_natCast_eq_neg_one_iff hs _).1 (by rw [hy']; exact hy.2.2)⟩
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hy', hy.2.1]
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
    exact ZMod.val_natCast_of_lt hx.1
  · intro y _
    exact ZMod.natCast_zmod_val y

/-- **At the top level** (`s = r`, the `b` with `d(b) = 1`): `x ↦ -x` identifies `β(M, a, r)` with
the number of square roots of `a` in `H = {h ∈ (ℤ/M)ˣ : h ≡ 1 (mod r)}`. -/
theorem sqrtCount_top' {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = (univ.filter fun h : ZMod M =>
      IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1).card := by
  rw [sqrtCount_eq_card_zmod hr]
  refine card_nbij' (fun y => -y) (fun y => -y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hy.1.neg, by rw [neg_sq]; exact hy.2.1, ?_⟩
    rw [map_neg, hy.2.2, neg_neg]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hy.1.neg, by rw [neg_sq]; exact hy.2.1, ?_⟩
    rw [map_neg, hy.2.2]
  · intro y _; exact neg_neg y
  · intro y _; exact neg_neg y

/-- **The class criterion at the top level.** `β(M, a, r)` is `0` unless `a` is the square of an
element of `H`, and then it equals `β(M, 1, r)`, the number of square roots of `1` in `H`. -/
theorem sqrtCount_top_dichotomy' {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = if ∃ h : ZMod M, IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1
      then sqrtCount M 1 r else 0 := by
  rw [sqrtCount_top' hr, sqrtCount_top' hr]
  split_ifs with hex
  · obtain ⟨h0, hu, hsq, hH⟩ := hex
    set u := hu.unit
    have hu0 : (u : ZMod M) = h0 := hu.unit_spec
    have hinvH : ZMod.castHom hr (ZMod r) ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      have h1 : ZMod.castHom hr (ZMod r) ((u⁻¹ : (ZMod M)ˣ) : ZMod M) *
          ZMod.castHom hr (ZMod r) (u : ZMod M) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rwa [hu0, hH, mul_one] at h1
    have hinvsq : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) ^ 2 * (a : ZMod M) = 1 := by
      rw [← hsq, ← hu0, ← mul_pow, Units.inv_mul, one_pow]
    refine card_nbij' (fun y => y * (u⁻¹ : (ZMod M)ˣ)) (fun y => y * u) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hy.1.mul (Units.isUnit _), ?_, ?_⟩
      · rw [mul_pow, hy.2.1, mul_comm, hinvsq, Nat.cast_one]
      · rw [map_mul, hy.2.2, hinvH, mul_one]
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hy.1.mul (Units.isUnit _), ?_, ?_⟩
      · rw [mul_pow, hy.2.1, Nat.cast_one, one_mul, hu0, hsq]
      · rw [map_mul, hy.2.2, hu0, hH, mul_one]
    · intro y _
      simp only [mul_assoc, Units.inv_mul, mul_one]
    · intro y _
      simp only [mul_assoc, Units.mul_inv, mul_one]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro y _ hy
    exact hex ⟨y, hy⟩

end ZModForm

section Imaginary

/-- If `x` is a unit modulo `2r` with `x² ≡ 1 + r (mod 2r)`, then `2^{v₂(r) + 1} ∤ x² - 1`. -/
lemma not_pow_succ_dvd_sq_sub_one {r x : ℕ} (hr : 0 < r)
    (hsq : x ^ 2 % (2 * r) = (1 + r) % (2 * r))
    (hdvd : ((2 ^ (r.factorization 2 + 1) : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - 1) : False := by
  set k := r.factorization 2
  have hk : 2 ^ k ∣ r := Nat.ordProj_dvd r 2
  have hP : 2 ^ (k + 1) ∣ 2 * r := by rw [pow_succ, mul_comm]; exact Nat.mul_dvd_mul_left 2 hk
  have hmod : ((2 * r : ℕ) : ℤ) ∣ ((1 + r : ℕ) : ℤ) - ((x ^ 2 : ℕ) : ℤ) :=
    (Nat.modEq_iff_dvd).1 hsq
  have h1 : ((2 ^ (k + 1) : ℕ) : ℤ) ∣ ((1 + r : ℕ) : ℤ) - ((x ^ 2 : ℕ) : ℤ) :=
    (Int.natCast_dvd_natCast.2 hP).trans hmod
  have h2 : ((2 ^ (k + 1) : ℕ) : ℤ) ∣ (r : ℤ) := by
    have := dvd_add h1 hdvd
    push_cast at this ⊢
    convert this using 1; ring
  exact Nat.pow_succ_factorization_not_dvd hr.ne' Nat.prime_two (Int.natCast_dvd_natCast.1 h2)

/-- **Imaginary families.** Let `r` be even, `M = 2r` and `a = 1 + r`. If `8 ∤ r` then
`β(2r, 1 + r, s) = 0` for every `s`. In general `β(2r, 1 + r, r/d) = 0` whenever `d ∣ r` is odd,
that is, the bias can be nonzero only for `b` whose exponent `d(b)` is even. -/
theorem sqrtCount_imaginary' {r : ℕ} (hr : 0 < r) (hev : Even r) :
    (¬ 8 ∣ r → ∀ s, sqrtCount (2 * r) (1 + r) s = 0) ∧
      (∀ d, d ∣ r → ¬ 2 ∣ d → sqrtCount (2 * r) (1 + r) (r / d) = 0) := by
  set k := r.factorization 2 with hkdef
  have hk1 : 0 < k := Nat.prime_two.factorization_pos_of_dvd hr.ne' (even_iff_two_dvd.1 hev)
  -- an element of the count is odd
  have hodd : ∀ x, Nat.Coprime x (2 * r) → Odd x := by
    intro x hx
    exact Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 r) hx)
  constructor
  · intro h8 s
    rw [sqrtCount, card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨hcop, hsq, -⟩
    obtain ⟨m, rfl⟩ := hodd x hcop
    have hk3 : k + 1 ≤ 3 := by
      by_contra hc
      apply h8
      exact (pow_dvd_pow 2 (by omega : 3 ≤ k)).trans (Nat.ordProj_dvd r 2)
    apply not_pow_succ_dvd_sq_sub_one hr hsq
    have h8x : (8 : ℤ) ∣ ((2 * m + 1 : ℕ) : ℤ) ^ 2 - 1 := by
      obtain ⟨j, hj⟩ := Int.even_mul_succ_self (m : ℤ)
      refine ⟨j, ?_⟩
      push_cast
      linear_combination 4 * hj
    refine dvd_trans ?_ h8x
    have : 2 ^ (k + 1) ∣ 8 := (pow_dvd_pow 2 hk3)
    exact_mod_cast this
  · intro d hd hdodd
    rw [sqrtCount, card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨-, hsq, hs⟩
    -- `2^k ∣ r/d` since `d` is odd
    have hks : 2 ^ k ∣ r / d := by
      have hrd : r = d * (r / d) := (Nat.mul_div_cancel' hd).symm
      have hcop : Nat.Coprime (2 ^ k) d :=
        Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).2 hdodd)
      exact hcop.dvd_of_dvd_mul_left (hrd ▸ Nat.ordProj_dvd r 2)
    obtain ⟨y, hy⟩ := hks.trans hs
    apply not_pow_succ_dvd_sq_sub_one hr hsq
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨(y : ℤ) * (2 ^ j * y - 1), ?_⟩
    have hxy : (x : ℤ) = 2 ^ k * y - 1 := by
      have : ((x + 1 : ℕ) : ℤ) = ((2 ^ k * y : ℕ) : ℤ) := by rw [hy]
      push_cast at this; linarith
    rw [hxy, ← hkdef, hj]
    push_cast
    ring

end Imaginary

/-- The predictions `β` of the table of Paper XI, Section 7 (families `p ≡ a (mod M)` and
`s = r/d(b)` for generic `b`, squares and fourth powers). -/
theorem sqrtCount_table' :
    -- r = 2
    sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 2 = 4 ∧ sqrtCount 8 5 2 = 0 ∧
    -- r = 3 (generic and squares: s = 3)
    sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 4 (generic s = 4, squares s = 2)
    sqrtCount 8 5 4 = 0 ∧ sqrtCount 8 5 2 = 0 ∧
    sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    -- r = 6 (generic s = 6, squares s = 3)
    sqrtCount 12 1 6 = 2 ∧ sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 6 = 0 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 8 (generic s = 8, squares s = 4, fourth powers s = 2)
    sqrtCount 16 1 8 = 2 ∧ sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧
    sqrtCount 16 9 8 = 0 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    sqrtCount 32 17 8 = 2 ∧ sqrtCount 32 17 4 = 2 ∧ sqrtCount 32 17 2 = 4 ∧
    sqrtCount 32 25 8 = 0 ∧ sqrtCount 32 25 4 = 2 ∧ sqrtCount 32 25 2 = 4 := by
  decide

end FixedOrderFactor
