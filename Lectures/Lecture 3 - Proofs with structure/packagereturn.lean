/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

-- delete right tactic portion to prove left side or delete left tactic portion to prove right side
example {d1 s1 d2 s2 x1 x2 : ℝ} (h1 : d1 = 5) (h2 : s1 = 50) (h3 : d2 = 1) (h4 : s2 = 30) 
(h5 : x1 = d1/s1) (h6 : x2 = d2/s2): x1 ≤ 0.3333 ∨ x2 ≤ 0.3333 := by
  left
  calc
    x1 = d1/s1 := by rw[h5]
    _ = 5/s1 := by rw [h1]
    _ = 5/50 := by rw [h2]
    _ ≤ 0.3333 := by numbers
  right
  calc
    x2 = d2/s2 := by rw[h6]
    _ = 1/s2 := by rw [h3]
    _ = 1/30 := by rw [h4]
    _ ≤ 0.3333 := by numbers 




