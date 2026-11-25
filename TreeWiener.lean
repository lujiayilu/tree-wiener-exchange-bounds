import Mathlib

/-! Real-valued exchange bounds in the coordinates of the path x--z--y.
The coordinates of an off-path vertex are its attachment coordinate r and
its height k. The tree-to-coordinate representation is an input. -/
namespace TreeWiener

/-- Contribution of one projected vertex to the chord surplus. -/
theorem chord (a b r k : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hr' : r ≤ a+b) :
    (if r = a then 2*a*b else 0) ≤
      b*(k+r) + a*(k+a+b-r) - (a+b)*(k+|r-a|) := by
  split_ifs with e
  · subst r
    simp only [sub_self, abs_zero, add_zero]
    linarith only [show b*(k+a)+a*(k+a+b-a)-(a+b)*k = 2*a*b by ring]
  · rcases le_total r a with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      nlinarith [mul_nonneg hb hr]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hr')]

/-- Sum of the single-vertex chord inequalities, including the fiber mass. -/
theorem chord_sum {ι : Type*} (S : Finset ι) (a b : ℝ) (m r k : ι → ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hr : ∀ i ∈ S, 0 ≤ r i ∧ r i ≤ a+b) :
    (∑ i ∈ S, m i * (if r i = a then 2*a*b else 0)) ≤
      ∑ i ∈ S, m i * (b*(k i+r i) + a*(k i+a+b-r i) -
        (a+b)*(k i+|r i-a|)) := by
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (chord a b (r i) (k i) ha hb (hr i hi).1 (hr i hi).2) (hm i hi)

/-- Separate the two exchange sites from all other unordered pairs.
A and B are potentials contributed by all remaining vertices. -/
def pairCost (x z A B d C : ℝ) := C + x*A + z*B + x*z*d

theorem transfer (x z A B d C t : ℝ) :
    pairCost (x-t) (z+t) A B d C - pairCost x z A B d C =
      t*((B+x*d)-(A+z*d))-t^2*d := by
  unfold pairCost
  ring

/-- Equation (1), with the chord estimate and directed gains as inputs. -/
theorem exchange (a b p q B σ Ux Uz Uy : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hc : 2*a*b*B ≤ b*Ux + a*Uy - (a+b)*Uz) :
    a*b*(2*B+σ*(p+q))/(b/p+a/q) ≤
      max (p*(Ux-Uz+σ*p*a)) (q*(Uy-Uz+σ*q*b)) := by
  let M := max (p*(Ux-Uz+σ*p*a)) (q*(Uy-Uz+σ*q*b))
  have hx : p*(Ux-Uz+σ*p*a) ≤ M := le_max_left _ _
  have hy : q*(Uy-Uz+σ*q*b) ≤ M := le_max_right _ _
  have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ b/p by positivity)
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ a/q by positivity)
  change _ ≤ M
  apply (div_le_iff₀ (show 0 < b/p+a/q by positivity)).2
  calc
    _ ≤ b*(Ux-Uz+σ*p*a)+a*(Uy-Uz+σ*q*b) := by nlinarith only [hc]
    _ = (b/p)*(p*(Ux-Uz+σ*p*a))+(a/q)*(q*(Uy-Uz+σ*q*b)) := by
      field_simp <;> ring
    _ ≤ _ := by nlinarith only [hx', hy']

/-- Common denominator estimate for both gaps in Theorem 2.
Use K=c+u+h for valleys and K=c+u for peaks. -/
theorem threshold (a b p q l h K N : ℝ) (hl : 0 < l) (hh : 0 < h)
    (ha : l ≤ a) (hb : l ≤ b) (hp : h ≤ p) (hq : h ≤ q)
    (hK : 0 ≤ K) (hN : 2*K ≤ N) :
    l*h*K ≤ a*b*N/(b/p+a/q) := by
  have pa := lt_of_lt_of_le hl ha
  have pb := lt_of_lt_of_le hl hb
  have pp := lt_of_lt_of_le hh hp
  have pq := lt_of_lt_of_le hh hq
  have xp : h*(b/p) ≤ b := by
    rw [show h*(b/p) = h*b/p by ring]
    exact (div_le_iff₀ pp).2 (by nlinarith [mul_nonneg pb.le (sub_nonneg.mpr hp)])
  have xq : h*(a/q) ≤ a := by
    rw [show h*(a/q) = h*a/q by ring]
    exact (div_le_iff₀ pq).2 (by nlinarith [mul_nonneg pa.le (sub_nonneg.mpr hq)])
  apply (le_div_iff₀ (show 0 < b/p+a/q by positivity)).2
  calc
    _ = (l*K)*(h*(b/p)+h*(a/q)) := by ring
    _ ≤ (l*K)*(b+a) := mul_le_mul_of_nonneg_left (add_le_add xp xq) (by positivity)
    _ ≤ (a*b)*(2*K) := by
      have h₁ := mul_le_mul_of_nonneg_right ha pb.le
      have h₂ := mul_le_mul_of_nonneg_right hb pa.le
      have hs : l*(b+a) ≤ 2*(a*b) := by nlinarith only [h₁,h₂]
      nlinarith only [mul_le_mul_of_nonneg_right hs hK]
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

/-- Sharpness witnesses, with equal edge lengths and baseline m=c+u. -/
def pathCost (l x z y : ℝ) := l*(x*z+z*y+2*x*y)

theorem sharp (l m h : ℝ) :
    pathCost l (m+h) m (m+h) - pathCost l m (m+h) (m+h) = l*h*(m+h) ∧
    pathCost l (m+h) m m - pathCost l m (m+h) m = l*h*m := by
  unfold pathCost
  constructor <;> ring

end TreeWiener
