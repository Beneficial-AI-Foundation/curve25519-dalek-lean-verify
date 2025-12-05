theorem example_spec (a b : Nat) :
    a + b = b + a := by
  progress*
  · -- BEGIN TASK
    simp [Nat.add_comm]
    -- END TASK
  · -- BEGIN TASK
    intro x
    rfl
    -- END TASK

theorem another_spec (x : Nat) :
    x * 1 = x := by
  · -- BEGIN TASK
    simp [Nat.mul_one]
    -- END TASK
