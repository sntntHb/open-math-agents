import OMAStatements.S_oeis_a066534
import Mathlib

/-!
# Proof of the Mathar recurrence for OEIS A066534

Credit: @sntntHb (the owner of the agent is credited as the solver)

Proof sketch. Splitting off the last summand and using `(n+1)!/k! = (n+1) * (n!/k!)` for
`k ≤ n` gives the first-order recurrence `a(n+1) = (n+1) a(n) + (n+1) 2^n`. Writing
`n = m + 3` and expressing `a(m+3)`, `a(m+2)`, `a(m+1)` through `a(m)` and `2^m` turns the
four-term recurrence into a polynomial identity, closed by `ring`.
-/

namespace OMA.P_oeis_a066534

open Finset OMA.S_oeis_a066534

theorem step (n : ℕ) : a (n + 1) = (n + 1) * a n + (n + 1) * 2 ^ n := by
  unfold a
  rw [sum_range_succ, mul_sum]
  have hlast : (n + 1).factorial / n.factorial = n + 1 := by
    rw [Nat.factorial_succ, Nat.mul_div_cancel _ (Nat.factorial_pos n)]
  rw [hlast]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simp at hk; omega
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hkn), mul_assoc]

end OMA.P_oeis_a066534

open OMA.S_oeis_a066534 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066534.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 := OMA.P_oeis_a066534.step m
  have h2 := OMA.P_oeis_a066534.step (m + 1)
  have h3 := OMA.P_oeis_a066534.step (m + 2)
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have h1' : (a (m + 1) : ℤ) = (m + 1) * a m + (m + 1) * 2 ^ m := by exact_mod_cast h1
  have h2' : (a (m + 2) : ℤ) = (m + 2) * a (m + 1) + (m + 2) * 2 ^ (m + 1) := by
    push_cast [h2]; ring
  have h3' : (a (m + 3) : ℤ) = (m + 3) * a (m + 2) + (m + 3) * 2 ^ (m + 2) := by
    push_cast [h3]; ring
  rw [h3', h2', h1']
  push_cast
  ring
