import Mathlib


example {ladder base building : ℝ} (h1 : ladder = 100) (h2 : base = 16)
 (h3 : building^2 = ladder^2 - base^2) : building^2 < 10000 := by
  calc
    building^2 = ladder^2 - base^2 := by rw [h3]
    _ = 100^2 - base^2 := by rw [h1]
    _ = 100^2 - 16^2 := by rw [h2]
    _ = 9744 := by ring
    _ < 10000 := by norm_num
