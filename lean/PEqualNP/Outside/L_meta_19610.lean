import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19610 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3382551 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.and, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 7]⟩,
    ⟨.or, [13, 14]⟩, ⟨.or, [15, 1]⟩, ⟨.not, [16]⟩, ⟨.or, [12, 17]⟩], 18⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
