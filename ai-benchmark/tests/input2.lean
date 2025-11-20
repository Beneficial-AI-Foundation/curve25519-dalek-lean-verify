namespace curve25519_dalek.edwards.EdwardsPoint

@[progress]
theorem as_projective_spec (e : EdwardsPoint) :
∃ q, edwards.EdwardsPoint.as_projective e = ok q ∧
q.X = e.X ∧ q.Y = e.Y ∧ q.Z = e.Z := by
unfold edwards.EdwardsPoint.as_projective
simp

end curve25519_dalek.edwards.EdwardsPoint
