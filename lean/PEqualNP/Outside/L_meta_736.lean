import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def reindex (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

private lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases lt : i < w.length
  · simp [List.getD, List.getElem?_append_left lt, Nat.ne_of_lt lt]
  · rw [List.getD, List.getElem?_append_right (by omega)]
    by_cases eq : i = w.length
    · simp [eq]
    · have a : w.length ≤ i := by omega
      have b : [b].length ≤ i - w.length := by simp; omega
      simp [eq, List.getD, List.getElem?_eq_none a, List.getElem?_eq_none b]

private lemma fold_preserves (phi : ℕ → ℕ) (n n' m : ℕ)
    (pin : ∀ t : ℕ, t < m → ∀ i : ℕ, phi i = n' + t ↔ i = n + t)
    (gs : List Gate) (t : ℕ) (w w' : List Bool)
    (ht : t + gs.length ≤ m) (hw : w.length = n + t) (hw' : w'.length = n' + t)
    (same : ∀ i, w'.getD (phi i) false = w.getD i false) :
    ∀ i, ((gs.map (reindex phi)).foldl extend w').getD (phi i) false =
      (gs.foldl extend w).getD i false := by
  induction gs generalizing t w w' with
  | nil => exact same
  | cons g rest ih =>
    have htm : t < m := by simp at ht; omega
    have hin :
        (g.inputs.map phi).map (fun j => w'.getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => same i)
    apply ih (t + 1) (extend w g) (extend w' (reindex phi g))
    · simp at ht
      omega
    · simp [extend, hw]; omega
    · simp [extend, hw']; omega
    · intro i
      simp only [extend, reindex, getD_snoc, hw, hw', hin, pin t htm i, same i]

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  classical
  open PEqualNP.Outside.L_meta_736 in
  open PEqualNP.CircuitLowerBounds in
  intro n n' O e _ image _ gates
  let m := gates.length
  let onInput (i : ℕ) := ∃ j : Fin n', (e j).val = i
  let psi (i : ℕ) : ℕ :=
    if h : onInput i then h.choose.val
    else if i < n then n'
    else if i < n + m then n' + 1 + (i - n) else n' + 1 + m
  have pin (t : ℕ) (ht : t < m) (i : ℕ) : psi i = (n' + 1) + t ↔ i = n + t := by
    unfold psi
    split
    next he =>
      have hj := he.choose.isLt
      have hi : i < n := he.choose_spec ▸ (e he.choose).isLt
      omega
    next _ =>
      split
      next hi => omega
      next hn =>
        split
        next h2 => omega
        next h2 =>
          constructor
          · omega
          · intro h
            exact (h2 (by omega)).elim
  refine ⟨psi, ?_⟩
  intro x x' hx hx' hO he
  let w0 : List Bool := extend x' { op := GateOp.and, inputs := [] }
  have hw0 : w0 = x' ++ [true] := by
    simp [w0, extend, GateOp.eval]
  have base (i : ℕ) : w0.getD (psi i) false = x.getD i false := by
    rw [hw0, getD_snoc]
    by_cases himage : onInput i
    · have hp : psi i = himage.choose.val := dite_eq_left himage
      have hlt : himage.choose.val < n' := himage.choose.isLt
      rw [hp, if_neg (by omega)]
      simpa only [himage.choose_spec] using (he himage.choose).symm
    · have hp : psi i = (if i < n then n' else if i < n + m then n' + 1 + (i - n) else n' + 1 + m) :=
        dite_eq_right himage
      by_cases iold : i < n
      · rw [hp, if_pos iold, if_pos hx'.symm]
        let k : Fin n := ⟨i, iold⟩
        have hk : k ∈ O := by
          by_contra hn
          obtain ⟨j, hj⟩ := (image k).mp hn
          exact himage ⟨j, congrArg Fin.val hj⟩
        exact (hO k hk).symm
      · have hge : n' + 1 ≤ psi i := by
          rw [hp, if_neg iold]; split <;> omega
        rw [if_neg (by omega)]
        have l1 : x'.getD (psi i) false = false := by
          simp [List.getD, List.getElem?_eq_none (show x'.length ≤ psi i by omega)]
        have l2 : x.getD i false = false := by
          simp [List.getD, List.getElem?_eq_none (show x.length ≤ i by omega)]
        rw [l1, l2]
  have hw0len : w0.length = n' + 1 + 0 := by rw [hw0]; simp [hx']
  have output := fold_preserves psi n (n' + 1) m pin gates 0 x w0
    (by simp [m]) (by simpa using hx) hw0len base
  constructor
  · exact output
  · intro o
    exact output o
