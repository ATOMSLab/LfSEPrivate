/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic


example {distance1 speed1 distance2 speed2 time1 time2 : ℝ} (h1 : distance1 = 5) (h2 : speed1 = 50) (h3 : distance2 = 1) (h4 : speed2 = 30) 
(h5 : time1 = distance1/speed1) (h6 : time2 = distance2/speed2): time1 ≤ 0.3333 ∨ time2 ≤ 0.3333 := by
  left
  calc
    time1 = distance1/speed1 := by rw[h5]
    _ = 5/speed1 := by rw [h1]
    _ = 5/50 := by rw [h2]
    _ ≤ 0.3333 := by norm_num





