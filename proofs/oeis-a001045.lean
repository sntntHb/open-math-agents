import OMAStatements.S_oeis_a001045
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: from the recurrence, a(n+1) = 2 a(n) + (-1)^n, hence 3 a(n) = 2^n - (-1)^n.
-- Fossaceca: multiples of 3 in (2^n, 2^(n+1)) number (2^(n+1)-1)/3 - 2^n/3, which equals a(n)
-- by a parity case split. Copeland: by induction, (A^n) i j = a(n) + [i = j] (-1)^n,
-- using A = J - I; the trace and diagonal claims follow from a(n) = 2 a(n-1) + (-1)^(n-1).

namespace OMA.A001045Proof

open OMA.S_oeis_a001045

theorem a_succ (n : ℕ) : a (n + 1) = 2 * a n + (-1) ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    show a (n + 1) + 2 * a n = 2 * a (n + 1) + (-1) ^ (n + 1)
    rw [ih, pow_succ]
    ring

theorem three_a (n : ℕ) : 3 * a n = 2 ^ n - (-1) ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [a_succ, pow_succ, pow_succ]
    linear_combination 2 * ih

theorem count_mult (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.Ioo N (2 * N)).filter (fun m => 3 ∣ m)).card = (2 * N - 1) / 3 - N / 3 := by
  have hsplit : (Finset.Ioc 0 (2 * N - 1)) = Finset.Ioc 0 N ∪ Finset.Ioo N (2 * N) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_Ioo]
    omega
  have hdisj : Disjoint (Finset.Ioc 0 N) (Finset.Ioo N (2 * N)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Ioc, Finset.mem_Ioo] at hx hy
    omega
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (2 * N - 1) 3
  have h2 := Nat.Ioc_filter_dvd_card_eq_div N 3
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj), h2] at h1
  omega

theorem part1 (n : ℕ) :
    ((((Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card : ℕ) : ℤ) = a n := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [h2, count_mult _ hpos]
  have h3 := three_a n
  have hc : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; rfl
  rw [← hc] at h3
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at h3
    omega
  · rw [ho.neg_one_pow] at h3
    omega

theorem entries (n : ℕ) : ∀ i j, (A ^ n) i j = a n + if i = j then (-1) ^ n else 0 := by
  induction n with
  | zero =>
    intro i j
    by_cases h : i = j
    · subst h; simp [a]
    · simp [a, h, Matrix.one_apply_ne h]
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, ih, ih, ih, a_succ]
    fin_cases i <;> fin_cases j <;> simp [A, pow_succ] <;> ring

theorem part2 (n : ℕ) (hn : 1 ≤ n) :
    (A ^ n).trace = 6 * a (n - 1) ∧
      (∀ i j, i ≠ j → (A ^ n) i j = a n) ∧
      (∀ i, (A ^ n) i i = if Even n then a n + 1 else a n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, entries, if_true,
      Nat.add_sub_cancel]
    rw [a_succ, pow_succ]
    ring
  · intro i j hij
    rw [entries, if_neg hij, add_zero]
  · intro i
    rw [entries, if_pos rfl]
    split_ifs with he
    · rw [he.neg_one_pow]
    · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow]
      ring

end OMA.A001045Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main :=
  ⟨OMA.A001045Proof.part1, OMA.A001045Proof.part2⟩
