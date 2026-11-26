import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19646 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3956829 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 6]⟩, ⟨.not, [13]⟩,
    ⟨.and, [12, 14]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩,
    ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
