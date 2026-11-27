import OMAStatements.S_oeis_a336838
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Problem: A336838, numerator of the arithmetic mean of the divisors of q^e (q the prime after p, e odd).
-- Proof sketch: q is odd, write q = 2c+1 and e+1 = 2k. Then sigma(q^e) = (q+1) T with
-- T = sum_{j<k} q^(2j), so the divisor mean is (c+1) T / k. With g = gcd((c+1) T, k) the reduced
-- numerator is (c+1) (T/g), so it suffices that g divides T. Prime by prime: if r divides c+1 then
-- q^2 = 1 mod r, and r^m | k gives r^m | sum_{j<k} x^j for any x = 1 mod r (induction on m using
-- the factorization of a geometric sum over a*b terms); otherwise r^m is coprime to c+1.

namespace A336838Proof

theorem geom_split (x a : ℕ) : ∀ b : ℕ,
    ∑ j ∈ Finset.range (a * b), x ^ j =
      (∑ j ∈ Finset.range a, x ^ j) * ∑ i ∈ Finset.range b, (x ^ a) ^ i := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, ← pow_mul]
    ring

theorem geom_dvd (r : ℕ) (hr : r.Prime) : ∀ m k x : ℕ, x % r = 1 % r → r ^ m ∣ k →
    r ^ m ∣ ∑ j ∈ Finset.range k, x ^ j := by
  intro m
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro k x hx hk
    obtain ⟨k', rfl⟩ : r ∣ k := (dvd_pow_self r (Nat.succ_ne_zero m)).trans hk
    have hk' : r ^ m ∣ k' := by
      rw [pow_succ, mul_comm] at hk
      exact Nat.dvd_of_mul_dvd_mul_left hr.pos hk
    rw [geom_split, pow_succ, mul_comm]
    apply mul_dvd_mul
    · have : (∑ j ∈ Finset.range r, x ^ j) % r = (∑ j ∈ Finset.range r, 1 ^ j) % r := by
        rw [Finset.sum_nat_mod]
        conv_rhs => rw [Finset.sum_nat_mod]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.pow_mod, hx, ← Nat.pow_mod]
      apply Nat.dvd_of_mod_eq_zero
      rw [this]
      simp
    · apply ih k' _ _ hk'
      rw [Nat.pow_mod, hx, ← Nat.pow_mod, one_pow]


end A336838Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a336838.main := by
  intro p q e hp hq hpq _ he
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  obtain ⟨c, hc⟩ : ∃ c, q = 2 * c + 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact ⟨q / 2, by omega⟩
  obtain ⟨k0, rfl⟩ := he
  have hh : (q + 1) / 2 = c + 1 := by omega
  rw [hh]
  set k := k0 + 1 with hk
  set T := ∑ j ∈ Finset.range k, (q ^ 2) ^ j with hT
  have hsum : ∑ d ∈ (q ^ (2 * k0 + 1)).divisors, d = 2 * ((c + 1) * T) := by
    rw [Nat.divisors_prime_pow hq, Finset.sum_map]
    have : 2 * k0 + 1 + 1 = 2 * k := by omega
    simp only [Function.Embedding.coeFn_mk]
    rw [this, A336838Proof.geom_split q 2 k]
    simp [Finset.sum_range_succ, hT]
    rw [hc]; ring
  have hcard : (q ^ (2 * k0 + 1)).divisors.card = 2 * k := by
    rw [Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]; omega
  have hkpos : 0 < k := by omega
  set g := Nat.gcd ((c + 1) * T) k with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hkpos
  have hgT : g ∣ T := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro r m hr hrm
    have h1 : r ^ m ∣ (c + 1) * T := hrm.trans (Nat.gcd_dvd_left _ _)
    have h2 : r ^ m ∣ k := hrm.trans (Nat.gcd_dvd_right _ _)
    by_cases hrh : r ∣ c + 1
    · obtain ⟨t, ht⟩ := hrh
      apply A336838Proof.geom_dvd r hr m k (q ^ 2) _ h2
      have : q ^ 2 = 1 + r * (t * (4 * c)) := by
        rw [hc]
        have : (2 * c + 1) ^ 2 = 1 + (c + 1) * (4 * c) := by ring
        rw [this, ht]; ring
      rw [this, Nat.add_mul_mod_self_left]
    · have hcop : Nat.Coprime (r ^ m) (c + 1) :=
        Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrh)
      exact hcop.dvd_of_dvd_mul_left h1
  have hgk : g ∣ k := Nat.gcd_dvd_right _ _
  obtain ⟨a, ha⟩ := hgT
  obtain ⟨b, hb⟩ := hgk
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0] at hb; omega
    · exact h0
  have hcop : Nat.Coprime ((c + 1) * a) b := by
    have := Nat.coprime_div_gcd_div_gcd (m := (c + 1) * T) (n := k) hgpos
    rw [← hgdef] at this
    have e1 : (c + 1) * T / g = (c + 1) * a := by
      rw [ha, mul_left_comm, Nat.mul_div_cancel_left _ hgpos]
    have e2 : k / g = b := by
      rw [hb, Nat.mul_div_cancel_left _ hgpos]
    rwa [e1, e2] at this
  have hmean : OMA.S_oeis_a336838.divisorMean (q ^ (2 * k0 + 1)) =
      (((c + 1) * a : ℕ) : ℤ) / ((b : ℕ) : ℤ) := by
    unfold OMA.S_oeis_a336838.divisorMean
    rw [hsum, hcard]
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    rw [show (k : ℚ) = g * b by exact_mod_cast hb, show (T : ℚ) = g * a by exact_mod_cast ha]
    field_simp
  rw [hmean, Rat.num_div_eq_of_coprime (by exact_mod_cast hbpos)
    (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hcop)]
  rw [Int.natAbs_natCast]
  exact Dvd.intro a rfl

