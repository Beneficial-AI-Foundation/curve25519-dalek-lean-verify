namespace curve25519_dalek.edwards.EdwardsPoint

@[progress]
theorem as_projective_spec (e : EdwardsPoint) :
∃ q, edwards.EdwardsPoint.as_projective e = ok q ∧
q.X = e.X ∧ q.Y = e.Y ∧ q.Z = e.Z := by
  -- BEGIN task 1
  sorry
  -- END task 1

end curve25519_dalek.edwards.EdwardsPoint
