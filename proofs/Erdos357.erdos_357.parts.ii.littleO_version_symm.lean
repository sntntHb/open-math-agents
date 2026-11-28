import FormalConjectures.ErdosProblems.«357»

-- Problem: Erdős Problem 357 — littleO version symm (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/357.lean (declaration
-- Erdos357.erdos_357.parts.ii.littleO_version_symm)
-- Credit: @sntntHb
-- Answer: n * log n. Whether f(n) = o(n) is the open first part of the problem, so no explicit
-- function of order n or below is known to work. The proof uses only the elementary bound
-- f(n) ≤ n (a strictly increasing sequence in [1, n] has at most n terms).

namespace OMA357

open Filter Asymptotics

theorem len_le {k n : ℕ} (a : Fin k → ℤ) (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ))
    (hm : StrictMono a) : k ≤ n := by
  have hsub : (Finset.univ.image a) ⊆ Finset.Icc (1 : ℤ) n := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (hr ⟨i, rfl⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hm.injective] at hcard
  simpa using hcard

theorem f_le (n : ℕ) : Erdos357.f n ≤ n := by
  unfold Erdos357.f
  apply csSup_le'
  rintro k ⟨a, hr, hm, -⟩
  exact len_le a hr hm

theorem natCast_isLittleO :
    (fun n : ℕ ↦ (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) := by
  have hlog : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := by
    apply (isLittleO_const_left).2
    right
    exact tendsto_norm_atTop_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop).mul_isLittleO hlog
  simpa using h

end OMA357

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ (n : ℝ) * Real.log (n : ℝ)

theorem OMA.solution : Erdos357.erdos_357.parts.ii.littleO_version_symm.answer = OMA.answer →
    type_of% @Erdos357.erdos_357.parts.ii.littleO_version_symm := by
  intro h
  rw [h]
  have h1 : (fun n : ℕ ↦ (Erdos357.f n : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    simp only [Real.norm_natCast, one_mul]
    exact_mod_cast OMA357.f_le n
  exact h1.trans_isLittleO OMA357.natCast_isLittleO
