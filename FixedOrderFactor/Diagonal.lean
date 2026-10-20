module

public import FixedOrderFactor.Values

@[expose] public section

open Real Filter Topology Finset
namespace FixedOrderFactor

/-- The terms of `zetaN`. -/
noncomputable def zterm (N : Finset Nat.Primes) (s n : ℕ) : ℝ :=
  if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0

/-- The weights of the coprime pairs. -/
noncomputable def pairTerm (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) : ℝ :=
  if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
  then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0

lemma zterm_nonneg (N : Finset Nat.Primes) (s n : ℕ) : 0 ≤ zterm N s n := by
  unfold zterm; split_ifs <;> positivity

lemma pairTerm_nonneg (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) : 0 ≤ pairTerm N r ab := by
  unfold pairTerm; split_ifs <;> positivity

lemma hasSum_zterm (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasSum (zterm N s) (zetaN N s) :=
  (summable_zetaN_terms N hs).hasSum

lemma summable_norm_zterm (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖zterm N s n‖) :=
  Summable.congr (summable_zetaN_terms N hs : Summable (zterm N s))
    (fun n => (Real.norm_of_nonneg (zterm_nonneg N s n)).symm)

lemma summable_prod_zterm (N : Finset Nat.Primes) {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    Summable (fun x : ℕ × ℕ => zterm N s x.1 * zterm N t x.2) := by
  exact summable_mul_of_summable_norm (summable_norm_zterm N hs) (summable_norm_zterm N ht)

lemma pairTerm_le (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) :
    pairTerm N r ab ≤ zterm N r ab.1 * zterm N r ab.2 := by
  unfold pairTerm zterm
  by_cases h : 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
  · rw [if_pos h, if_pos ⟨h.1, h.2.2.2.1⟩, if_pos ⟨h.2.1, h.2.2.2.2⟩]
    push_cast; rw [mul_pow]; field_simp; rfl
  · rw [if_neg h]; exact mul_nonneg (zterm_nonneg N r _) (zterm_nonneg N r _)

lemma summable_pairTerm (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Summable (pairTerm N r) :=
  Summable.of_nonneg_of_le (pairTerm_nonneg N r) (pairTerm_le N r) (summable_prod_zterm N hr hr)

lemma primeTo_of_dvd {N : Finset Nat.Primes} {m n : ℕ} (h : PrimeTo N n) (hmn : m ∣ n) :
    PrimeTo N m := fun q hq hqm => h q hq (hqm.trans hmn)

lemma zterm_ne_zero {N : Finset Nat.Primes} {s n : ℕ} (h : zterm N s n ≠ 0) :
    0 < n ∧ PrimeTo N n := by
  unfold zterm at h; split_ifs at h with h'; exacts [h', absurd rfl h]

lemma pairTerm_ne_zero {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ} (h : pairTerm N r ab ≠ 0) :
    0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2 := by
  unfold pairTerm at h; split_ifs at h with h'; exacts [h', absurd rfl h]

lemma zterm_of {N : Finset Nat.Primes} {s n : ℕ} (h0 : 0 < n) (h : PrimeTo N n) :
    zterm N s n = 1 / (n : ℝ) ^ s := by
  unfold zterm; rw [if_pos ⟨h0, h⟩]

lemma pairTerm_of {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ}
    (h : 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2) :
    pairTerm N r ab = 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r := by
  unfold pairTerm; rw [if_pos h]

theorem hasSum_coprime_pairs' (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (pairTerm N r) (correctionFactor N r) := by
  set S := ∑' ab, pairTerm N r ab
  have hS : HasSum (pairTerm N r) S := (summable_pairTerm N hr).hasSum
  -- `ζ(r)² = Σ_{a,b} a⁻ʳ b⁻ʳ`
  have h1 : HasSum (fun x : ℕ × ℕ => zterm N r x.1 * zterm N r x.2) (zetaN N r * zetaN N r) :=
    (hasSum_zterm N hr).mul (hasSum_zterm N hr) (summable_prod_zterm N hr hr)
  -- `ζ(2r) S = Σ_{d,(a,b)} d⁻²ʳ w(a,b)`
  have hG : HasSum (fun x : ℕ × (ℕ × ℕ) => zterm N (2 * r) x.1 * pairTerm N r x.2)
      (zetaN N (2 * r) * S) := by
    refine (hasSum_zterm N (by omega)).mul hS ?_
    refine summable_mul_of_summable_norm (summable_norm_zterm N (by omega)) ?_
    exact Summable.congr (summable_pairTerm N hr)
      (fun n => (Real.norm_of_nonneg (pairTerm_nonneg N r n)).symm)
  -- reindex by `(d, (a, b)) ↦ (d a, d b)`
  have hbij : HasSum (fun x : ℕ × ℕ => zterm N r x.1 * zterm N r x.2) (zetaN N (2 * r) * S) := by
    refine (hasSum_iff_hasSum_of_ne_zero_bij
      (g := fun x : ℕ × (ℕ × ℕ) => zterm N (2 * r) x.1 * pairTerm N r x.2)
      (fun x => ((x : ℕ × (ℕ × ℕ)).1 * x.1.2.1, (x : ℕ × (ℕ × ℕ)).1 * x.1.2.2))
      ?_ ?_ ?_).mpr hG
    · rintro ⟨⟨d, a, b⟩, hx⟩ ⟨⟨d', a', b'⟩, hy⟩ h
      have hx' := mul_ne_zero_iff.mp hx
      have hy' := mul_ne_zero_iff.mp hy
      obtain ⟨hd, -⟩ := zterm_ne_zero hx'.1
      obtain ⟨hd', -⟩ := zterm_ne_zero hy'.1
      obtain ⟨-, -, hab, -, -⟩ := pairTerm_ne_zero hx'.2
      obtain ⟨-, -, hab', -, -⟩ := pairTerm_ne_zero hy'.2
      simp only [Prod.mk.injEq] at h
      have hdd : d = d' := by
        have e1 : Nat.gcd (d * a) (d * b) = d := by rw [Nat.gcd_mul_left, hab, mul_one]
        have e2 : Nat.gcd (d' * a') (d' * b') = d' := by rw [Nat.gcd_mul_left, hab', mul_one]
        rw [← e1, ← e2, h.1, h.2]
      subst hdd
      have ha := Nat.eq_of_mul_eq_mul_left hd h.1
      have hb := Nat.eq_of_mul_eq_mul_left hd h.2
      subst ha; subst hb; rfl
    · rintro ⟨a, b⟩ hab
      have hab' := mul_ne_zero_iff.mp hab
      obtain ⟨ha0, haN⟩ := zterm_ne_zero hab'.1
      obtain ⟨hb0, hbN⟩ := zterm_ne_zero hab'.2
      set d := Nat.gcd a b
      have hd : 0 < d := Nat.gcd_pos_of_pos_left b ha0
      have hda : d ∣ a := Nat.gcd_dvd_left a b
      have hdb : d ∣ b := Nat.gcd_dvd_right a b
      have ha' : 0 < a / d := Nat.div_pos (Nat.le_of_dvd ha0 hda) hd
      have hb' : 0 < b / d := Nat.div_pos (Nat.le_of_dvd hb0 hdb) hd
      have hcop : Nat.Coprime (a / d) (b / d) := Nat.coprime_div_gcd_div_gcd hd
      have hG : zterm N (2 * r) d * pairTerm N r (a / d, b / d) ≠ 0 := by
        rw [zterm_of hd (primeTo_of_dvd haN hda),
          pairTerm_of ⟨ha', hb', hcop, primeTo_of_dvd haN (Nat.div_dvd_of_dvd hda),
            primeTo_of_dvd hbN (Nat.div_dvd_of_dvd hdb)⟩]
        have : 0 < a / d * (b / d) := Nat.mul_pos ha' hb'
        positivity
      refine ⟨⟨(d, (a / d, b / d)), hG⟩, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb⟩
    · rintro ⟨⟨d, a, b⟩, hx⟩
      have hx' := mul_ne_zero_iff.mp hx
      obtain ⟨hd, hdN⟩ := zterm_ne_zero hx'.1
      have hp := pairTerm_ne_zero hx'.2
      obtain ⟨ha, hb, -, haN, hbN⟩ := id hp
      simp only
      rw [zterm_of (Nat.mul_pos hd ha) ((primeTo_mul_iff N d a).mpr ⟨hdN, haN⟩),
        zterm_of (Nat.mul_pos hd hb) ((primeTo_mul_iff N d b).mpr ⟨hdN, hbN⟩),
        zterm_of hd hdN, pairTerm_of hp]
      push_cast
      have : (0 : ℝ) < d := by exact_mod_cast hd
      have : (0 : ℝ) < a := by exact_mod_cast ha
      have : (0 : ℝ) < b := by exact_mod_cast hb
      field_simp
      ring
  have heq := h1.unique hbij
  have hZ := (zetaN_pos N (by omega : 2 ≤ 2 * r)).ne'
  have : S = correctionFactor N r := by
    unfold correctionFactor; rw [sq, heq]; field_simp
  rw [← this]; exact hS

end FixedOrderFactor
