import Mathlib

/- A toy mouse changes speed from a constant 2 m/s to 0 m/s in the span of two seconds. It's mass is
  estimated to be around 0.1 kg. The toy can only handle two Newtons of force. Prove that the force
  it experiences is below this limit. -/

theorem toy_mouse_force_limit {f :ℝ }
(h1:v₀=2)
(h2:v₁=0)
(h3:m=0.1)
(h4:t=2)
(h5:a=(v₁ - v₀) / t)
(h6:f= m *a) :f < 2 := by
calc
f=m * a := by rw[h6]
_=m*((v₁ - v₀) / t ):= by rw [h5]
_= m*((0  - 2) / 2 ) := by rw[h2,h1,h4]
_=0.1*-1:=by rw[h3];ring
_=-0.1 :=by ring
_<2 :=by norm_num


/- A ball is dropped from a height of three meters with no initial velocity. Prove that it takes
  less than one second for it to hit the ground. -/
theorem less_3ms {d t v:ℝ }
(h1:d=3)
(h2:v₀=0)
(h3:a=9.8)
(ho:t=d/a)
: t<1:=
calc
t=d/a := by rw[ho]
_=3/9.8 := by rw[h1,h3];
_<1 :=by norm_num

/- 1.Prove there does not exist a resistor with resistance x such that when placed in parallel with
   itself will obtain the same total resistance as when placed in series. basically use two resistance addition equations and prove that they will never be equal  -/

example :1/0=0:= by norm_num
 /- Note : Technically, there does exist a real number that allows parallel resistance to equal
  series; that number is zero. However, 1 / 0 in Lean just calculates to 0 which does not correlate
  with the real world. Additionally, zero and negative resistance(as far as I know) don't exist.
-/


/- 2.Hooke's Law states that the force of a compressed / stretched spring is proportional to the
   distance from equilibrium. Prove that the force of the spring is the negative derivative of the
   energy with respect to the distance.
-/


/-  3.A charged particle is moving in a uniform magnetic field.
 derive the equation of motion for the particle, showing that it undergoes circular motion. -/


/- 4.a capacitor with capacitance C is charged with a voltage V.
 calculate the energy stored in the capacitor, and explain the significance of this energy. -/

-- The energy stored in a capacitor is potential energy, which can be used to do work

--  5.Two point charges, q1 and q2, are separated by a distance r.
-- Calculate the electric field at a point midway between the charges, and express it in terms of the charges and the distance.


--  6.A thin lens has a focal length of 10 cm. If an object is placed 20 cm from the lens,
-- find the position and magnification of the image formed.


-- 7.a wave traveling on a string has a wavelength of 2 meters and a frequency of 3 Hz.
-- Calculate the speed of the wave and the period of oscillation.


--  8.a rigid body is rotating about a fixed axis with an angular velocity ω.
-- Derive an expression for the kinetic energy of the rigid body in terms of its moment of inertia and angular velocity. --/
