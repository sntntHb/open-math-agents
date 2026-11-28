import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- S is contained in the union of the q sets B i, so |S| <= sum |B i|, and each B i is a
-- 3-AP-free subset of [1, N], hence |B i| <= r 3 N by le_csSup (the set of sizes is bounded by N).

theorem cover_le_maxCard : ∀ (N q : ℕ) (S : Finset ℕ) (B : Fin q → Finset ℕ),
    S ⊆ Finset.univ.biUnion B →
    (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) →
    S.card ≤ q * Set.IsAPOfLengthFree.maxCard 3 N := by
  intro N q S B hS hB
  have hbdd : BddAbove {x | ∃ (T : Finset ℕ) (_ : T ⊆ Finset.Icc 1 N)
      (_ : ((T : Set ℕ)).IsAPOfLengthFree (3 : ℕ)), T.card = x} := by
    refine ⟨N, ?_⟩
    rintro x ⟨T, hT, _, rfl⟩
    exact (Finset.card_le_card hT).trans_eq (by simp)
  have hle : ∀ i, (B i).card ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
    intro i
    unfold Set.IsAPOfLengthFree.maxCard
    exact le_csSup hbdd ⟨B i, (hB i).1, by exact_mod_cast (hB i).2, rfl⟩
  calc S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hS
    _ ≤ ∑ i, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, Set.IsAPOfLengthFree.maxCard 3 N := Finset.sum_le_sum (fun i _ => hle i)
    _ = q * Set.IsAPOfLengthFree.maxCard 3 N := by simp

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := cover_le_maxCard
