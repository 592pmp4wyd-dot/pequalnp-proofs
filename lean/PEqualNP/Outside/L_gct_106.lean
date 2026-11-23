import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_106 :
    ∀ (p q : ℕ) (t : Fin p → Fin q → ℂ), (∀ i, ∑ j, t i j = 0) → (∀ j, ∑ i, t i j = 0) → (∑ i, ∑ k, ∑ m, ∑ j, ∑ l, ∑ n, if i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n then 0 else t i j * t k l * t m n) = 4 * ∑ i, ∑ j, t i j ^ 3 := by
  intro p q t hrow hcol
  have triple : ∀ {r : ℕ} (a b c : Fin r → ℂ), (∑ x, a x = 0) → (∑ x, b x = 0) → (∑ x, c x = 0) →
      (∑ x, ∑ y, ∑ z, if x = y ∨ x = z ∨ y = z then (0 : ℂ) else a x * b y * c z)
        = 2 * ∑ x, a x * b x * c x := by
    intro r a b c ha hb hc
    have inner : ∀ x y, (∑ z, if x = y ∨ x = z ∨ y = z then (0 : ℂ) else a x * b y * c z)
        = if x = y then 0 else a x * b y * (-(c x) - c y) := by
      intro x y
      by_cases hxy : x = y
      · simp [hxy]
      · have h : ∀ z, (if x = y ∨ x = z ∨ y = z then (0 : ℂ) else a x * b y * c z)
            = a x * b y * c z - (if x = z then a x * b y * c x else 0)
              - (if y = z then a x * b y * c y else 0) := by
          intro z
          by_cases h1 : x = z
          · subst h1; simp [hxy, Ne.symm hxy]
          · by_cases h2 : y = z
            · subst h2; simp [hxy]
            · simp [hxy, h1, h2]
        rw [Finset.sum_congr rfl (fun z _ => h z)]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hc]
        simp [hxy]
        ring
    have mid : ∀ x, (∑ y, ∑ z, if x = y ∨ x = z ∨ y = z then (0 : ℂ) else a x * b y * c z)
        = 2 * (a x * b x * c x) - a x * ∑ y, b y * c y := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => inner x y)]
      have h : ∀ y, (if x = y then (0 : ℂ) else a x * b y * (-(c x) - c y))
          = (-(a x * c x) * b y - a x * (b y * c y))
            - (if x = y then (-(a x * c x) * b x - a x * (b x * c x)) else 0) := by
        intro y
        by_cases h1 : x = y
        · subst h1; simp
        · simp [h1]; ring
      rw [Finset.sum_congr rfl (fun y _ => h y)]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb]
      simp
      ring
    rw [Finset.sum_congr rfl (fun x _ => mid x)]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ha, ← Finset.mul_sum]
    ring
  have step1 : ∀ i k m, (∑ j, ∑ l, ∑ n, if i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n then (0 : ℂ) else t i j * t k l * t m n)
      = ∑ j, 2 * (if i = k ∨ i = m ∨ k = m then (0 : ℂ) else t i j * t k j * t m j) := by
    intro i k m
    by_cases hr : i = k ∨ i = m ∨ k = m
    · have : ∀ j l n : Fin q, (i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n) := by
        intro j l n; rcases hr with h | h | h <;> simp [h]
      simp [hr, this]
    · have e : ∀ j l n : Fin q, (i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n) ↔ (j = l ∨ j = n ∨ l = n) := by
        intro j l n; tauto
      simp only [e, hr, ite_false]
      rw [triple (t i) (t k) (t m) (hrow i) (hrow k) (hrow m),
        Finset.mul_sum]
  simp_rw [step1]
  -- move j outward
  have swap : (∑ i, ∑ k, ∑ m, ∑ j, 2 * (if i = k ∨ i = m ∨ k = m then (0 : ℂ) else t i j * t k j * t m j))
      = ∑ j, 2 * ∑ i, ∑ k, ∑ m, (if i = k ∨ i = m ∨ k = m then (0 : ℂ) else t i j * t k j * t m j) := by
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
  rw [swap]
  calc _ = ∑ j, 2 * (2 * ∑ i, t i j * t i j * t i j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h := triple (fun i => t i j) (fun i => t i j) (fun i => t i j) (hcol j) (hcol j) (hcol j)
        exact congrArg (2 * ·) h
    _ = ∑ j, 4 * ∑ i, t i j ^ 3 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← mul_assoc]; norm_num [pow_three, mul_assoc]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
