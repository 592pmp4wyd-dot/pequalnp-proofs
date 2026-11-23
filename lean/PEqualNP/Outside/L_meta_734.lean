import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_734

theorem fin2_eq (a b k : Fin 2) (ha : a ≠ k) (hb : b ≠ k) : a = b := by
  revert a b k; decide

theorem fin2_flip (a b k : Fin 2) (ha : a ≠ k) (hb : b ≠ a) : b = k := by
  revert a b k; decide

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin 2))
    (hC4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hdeg : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (T : Finset (Fin n)) (k : Fin 2) (hP : (T.filter (fun v => c v = k)).card ≤ 2)
    (z : Fin n → Fin n) (hz : ∀ v ∈ T, G.Adj v (z v) ∧ z v ∉ T) :
    ∃ J : Finset (Fin n), (∀ a ∈ J, a ∉ T) ∧ (∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b) ∧
      ∀ v, v ∉ J → ∃ u ∈ J, G.Adj v u := by
  classical
  set P := T.filter (fun v => c v = k) with hPdef
  set Z := P.image z with hZdef
  have hZT : ∀ y ∈ Z, y ∉ T := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact (hz p (Finset.mem_filter.mp hp).1).2
  have hZc : ∀ y ∈ Z, c y ≠ k := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have hp' := Finset.mem_filter.mp hp
    have := c.valid (hz p hp'.1).1
    rw [hp'.2] at this
    exact fun e => this e.symm
  have hZcard : Z.card ≤ 2 := le_trans Finset.card_image_le hP
  have claim : ∀ q ∈ T, c q ≠ k → ∃ w, G.Adj q w ∧ w ∉ T ∧ ∀ y ∈ Z, ¬ G.Adj w y := by
    intro q hq hqk
    by_contra hcon
    push Not at hcon
    have hall : ∀ w, G.Adj q w → ∃ y ∈ Z, G.Adj w y := by
      intro w hw
      by_cases hwT : w ∈ T
      · have hcw : c w = k := fin2_flip (c q) (c w) k hqk (fun e => c.valid hw e.symm)
        refine ⟨z w, Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hwT, hcw⟩, rfl⟩, ?_⟩
        exact (hz w hwT).1
      · exact hcon w hw hwT
    choose! f hf using hall
    set Nq := Finset.univ.filter (fun w => G.Adj q w) with hNq
    have hNcard : 3 ≤ Nq.card := by
      have h3 := hdeg q
      have e : {w : Fin n | G.Adj q w} = (Nq : Set (Fin n)) := by
        ext w; simp [hNq]
      rw [e, Set.ncard_coe_finset] at h3
      exact h3
    have hle : Nq.card ≤ Z.card := by
      apply Finset.card_le_card_of_injOn f
      · intro w hw
        exact (hf w (Finset.mem_filter.mp hw).2).1
      · intro w1 hw1 w2 hw2 heq
        have a1 := (Finset.mem_filter.mp hw1).2
        have a2 := (Finset.mem_filter.mp hw2).2
        have b1 := (hf w1 a1).2
        have b2 := (hf w2 a2).2
        have hyZ := (hf w1 a1).1
        rw [heq] at b1
        rcases hC4 q w1 (f w2) w2 a1 b1 b2.symm a2.symm with h | h
        · exact absurd hq (h ▸ hZT _ (heq ▸ hyZ))
        · exact h
    omega
  choose! w hw using claim
  set Q := T.filter (fun v => c v ≠ k) with hQdef
  set W := Q.image w with hWdef
  have hWc : ∀ x ∈ W, c x = k := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hq' := Finset.mem_filter.mp hq
    exact fin2_flip (c q) (c (w q)) k hq'.2 (fun e => c.valid (hw q hq'.1 hq'.2).1 e.symm)
  set S := Z ∪ W with hSdef
  have hSind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b := by
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact c.valid hab (fin2_eq _ _ k (hZc a ha) (hZc b hb))
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
      have hq' := Finset.mem_filter.mp hq
      exact (hw q hq'.1 hq'.2).2.2 a ha hab.symm
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      have hq' := Finset.mem_filter.mp hq
      exact (hw q hq'.1 hq'.2).2.2 b hb hab
    · exact c.valid hab ((hWc a ha).trans (hWc b hb).symm)
  have hST : ∀ a ∈ S, a ∉ T := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hZT a ha
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      have hq' := Finset.mem_filter.mp hq
      exact (hw q hq'.1 hq'.2).2.1
  have hdom : ∀ t ∈ T, ∃ s ∈ S, G.Adj t s := by
    intro t ht
    by_cases htk : c t = k
    · exact ⟨z t, Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, htk⟩, rfl⟩), (hz t ht).1⟩
    · exact ⟨w t, Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, htk⟩, rfl⟩), (hw t ht htk).1⟩
  set F := (Finset.univ : Finset (Fin n)).powerset.filter
    (fun J => S ⊆ J ∧ (∀ a ∈ J, a ∉ T) ∧ ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b) with hF
  have hSF : S ∈ F := by
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), subset_refl _, hST, hSind⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image F Finset.card ⟨S, hSF⟩
  rw [hF, Finset.mem_filter] at hJ
  obtain ⟨-, hSJ, hJT, hJind⟩ := hJ
  refine ⟨J, hJT, hJind, ?_⟩
  intro v hv
  by_cases hvT : v ∈ T
  · obtain ⟨s, hs, hadj⟩ := hdom v hvT
    exact ⟨s, hSJ hs, hadj⟩
  · by_contra hcon
    push Not at hcon
    have hmem : insert v J ∈ F := by
      rw [hF, Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        hSJ.trans (Finset.subset_insert _ _), ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hvT
        · exact hJT a ha
      · intro a ha b hb
        rcases Finset.mem_insert.mp ha with h1 | ha' <;>
          rcases Finset.mem_insert.mp hb with h2 | hb'
        · subst h1; subst h2; exact G.irrefl
        · subst h1; exact hcon b hb'
        · subst h2; exact fun h => hcon a ha' h.symm
        · exact hJind a ha' b hb'
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hv] at this
    omega

end PEqualNP.Outside.L_meta_734

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  intro n G hcol hC4 hdeg T hT hmis
  by_contra hno
  push Not at hno
  choose! z hz using hno
  obtain ⟨c⟩ := hcol
  set Tf := T.toFinset with hTf
  have hTcard : Tf.card ≤ 5 := by
    rw [hTf, ← Set.ncard_eq_toFinset_card']; exact hT
  have hz' : ∀ v ∈ Tf, G.Adj v (z v) ∧ z v ∉ Tf := by
    intro v hv
    rw [Set.mem_toFinset] at hv
    have := hz v hv
    exact ⟨this.1, by rw [Set.mem_toFinset]; exact this.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Tf) (fun v => c v = 0)
  have hk : ∃ k : Fin 2, (Tf.filter (fun v => c v = k)).card ≤ 2 := by
    by_cases h0 : (Tf.filter (fun v => c v = 0)).card ≤ 2
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have e : Tf.filter (fun v => c v = 1) = Tf.filter (fun v => ¬ c v = 0) := by
        apply Finset.filter_congr
        intro v _
        constructor
        · intro h; rw [h]; decide
        · intro h; exact PEqualNP.Outside.L_meta_734.fin2_flip 0 (c v) 1 (by decide) h
      rw [e]; omega
  obtain ⟨k, hkP⟩ := hk
  obtain ⟨J, hJT, hJind, hJmax⟩ :=
    PEqualNP.Outside.L_meta_734.main n G c hC4 hdeg Tf k hkP z hz'
  obtain ⟨t, htT, htI⟩ := hmis (J : Set (Fin n))
    (fun u hu v hv => hJind u hu v hv)
    (fun v hv => by
      obtain ⟨u, hu, h⟩ := hJmax v hv
      exact ⟨u, hu, h⟩)
  exact hJT t htI (by rw [hTf, Set.mem_toFinset]; exact htT)
