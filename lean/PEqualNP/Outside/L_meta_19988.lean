import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19988 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  refine ⟨⟨[⟨.or, [10, 11]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [0, 17]⟩, ⟨.and, [4, 18]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [22, 12]⟩, ⟨.or, [22, 10]⟩, ⟨.and, [1, 23]⟩, ⟨.and, [3, 24]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [28, 8]⟩, ⟨.and, [2, 29]⟩, ⟨.and, [7, 30]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [34, 11]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [5, 35]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [21, 27]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [40, 41]⟩], 42⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
