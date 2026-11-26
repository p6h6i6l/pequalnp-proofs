import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_23650 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34741 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  -- Positive singleton seed and the extra pair, with a safe two-bank exclusion.
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [8, 12]⟩],
    13⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
