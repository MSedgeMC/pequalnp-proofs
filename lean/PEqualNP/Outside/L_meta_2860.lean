import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default _ _ (by simp; omega)]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_take_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (X : List Bool) :
    wf (gs.take (k + 1)) X =
      wf (gs.take k) X ++ [gs[k].op.eval (gs[k].inputs.map fun i => (wf (gs.take k) X).getD i false)] := by
  rw [List.take_succ]
  have hopt : gs[k]?.toList = [gs[k]] := by simp [hk]
  rw [hopt, wf_append, wf_cons]
  rfl

theorem snoc_lt_pref (gs : List Gate) (k : ℕ) (hk : k < gs.length) (X : List Bool)
    (v : Bool) (w : ℕ) (hw : w < X.length + k) :
    (wf (gs.take k) X ++ [v]).getD w false = (wf (gs.take k) X).getD w false := by
  apply getD_snoc_lt
  rw [wf_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  exact hw

theorem snoc_gt_pref (gs : List Gate) (k : ℕ) (hk : k < gs.length) (X : List Bool)
    (v : Bool) (w : ℕ) (hw : X.length + k < w) :
    (wf (gs.take k) X ++ [v]).getD w false = false := by
  apply getD_snoc_gt
  rw [wf_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  exact hw

theorem take_set_self_of_le (l : List Gate) (i t : ℕ) (ht : t ≤ i) (a : Gate) :
    (l.set i a).take t = l.take t := by
  rw [List.take_set]
  rw [List.set_eq_take_append_cons_drop]
  simp only [List.length_take]
  by_cases h : i < min t l.length
  · have hfalse : False := by omega
    exact False.elim hfalse
  · simp [h]

theorem gateAt_set_self (gs : List Gate) (i : ℕ) (g : Gate) (hi : i < gs.length) :
    gateAt ⟨gs.set i g, 0⟩ i = g := by
  unfold gateAt
  have hlen : (gs.set i g).length = gs.length := by simp
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
  simp [List.getElem_set]

theorem gateAt_set_ne (gs : List Gate) (i j : ℕ) (g : Gate) (hi : i < gs.length)
    (hj : j < gs.length) (hji : j ≠ i) :
    gateAt ⟨gs.set i g, 0⟩ j = gateAt ⟨gs, 0⟩ j := by
  unfold gateAt
  have hlen : (gs.set i g).length = gs.length := by simp
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
  rw [List.getD_eq_getElem _ _ hj]
  have hij : i ≠ j := Ne.symm hji
  simp [List.getElem_set, hij]

theorem factor_ident (Z A B : Bool) :
    GateOp.and.eval [GateOp.or.eval [Z, A], GateOp.or.eval [Z, B]] =
      GateOp.or.eval [Z, GateOp.and.eval [A, B]] := by
  cases Z <;> cases A <;> cases B <;> simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2860

set_option maxHeartbeats 0 in
open PEqualNP.Outside.L_meta_2860 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  m < C.gates.length →
  n ≤ u →
  u < v →
  v < n + m →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] →
  (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) →
  C.output ≠ v →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m u v z a b hrb hm_len hnu huv hvn hm_op hm_in hu_op hu_in hv_op hv_in hread hout
  let k := v - n
  let ku := u - n
  let gv : Gate := ⟨GateOp.and, [a, b]⟩
  let gm : Gate := ⟨GateOp.or, [z, v]⟩
  let gs' : List Gate := (C.gates.set k gv).set m gm
  have hnv : n ≤ v := le_trans hnu (le_of_lt huv)
  have hk_wire : n + k = v := by dsimp [k]; omega
  have hku_wire : n + ku = u := by dsimp [ku]; omega
  have hlen : gs'.length = C.gates.length := by simp [gs']
  have hk_lt : k < C.gates.length := by
    by_contra h
    have hk_ge : C.gates.length ≤ k := Nat.le_of_not_gt h
    have hgat : gateAt C k = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      rw [List.getD_eq_default _ _ (by simpa using hk_ge)]
    have hin : (gateAt C k).inputs = [] := by rw [hgat]
    have hk_in : (gateAt C k).inputs = [z, b] := by simpa [k] using hv_in
    rw [hk_in] at hin
    simp at hin
  have hku_lt : ku < C.gates.length := by
    by_contra h
    have hku_ge : C.gates.length ≤ ku := Nat.le_of_not_gt h
    have hgat : gateAt C ku = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      rw [List.getD_eq_default _ _ (by simpa using hku_ge)]
    have hin : (gateAt C ku).inputs = [] := by rw [hgat]
    have hku_in : (gateAt C ku).inputs = [z, a] := by simpa [ku] using hu_in
    rw [hku_in] at hin
    simp at hin
  have hku_lt_k : ku < k := by dsimp [ku, k]; omega
  have hk_lt_m : k < m := by dsimp [k]; omega
  have hu_lt_m : u < n + m := by omega
  have hm_len' : m < gs'.length := by rw [hlen]; exact hm_len
  have hk_len' : k < gs'.length := by rw [hlen]; exact hk_lt
  have hku_len' : ku < gs'.length := by rw [hlen]; exact hku_lt
  have hgat_m : gateAt C m = ⟨GateOp.and, [u, v]⟩ := by
    rw [show gateAt C m = ⟨(gateAt C m).op, (gateAt C m).inputs⟩ by rfl]
    rw [hm_op, hm_in]
  have hgat_ku : gateAt C ku = ⟨GateOp.or, [z, a]⟩ := by
    rw [show gateAt C ku = ⟨(gateAt C ku).op, (gateAt C ku).inputs⟩ by rfl]
    rw [show (gateAt C ku).op = GateOp.or by simpa [ku] using hu_op]
    rw [show (gateAt C ku).inputs = [z, a] by simpa [ku] using hu_in]
  have hgat_k : gateAt C k = ⟨GateOp.or, [z, b]⟩ := by
    rw [show gateAt C k = ⟨(gateAt C k).op, (gateAt C k).inputs⟩ by rfl]
    rw [show (gateAt C k).op = GateOp.or by simpa [k] using hv_op]
    rw [show (gateAt C k).inputs = [z, b] by simpa [k] using hv_in]
  have hgm : C.gates[m] = ⟨GateOp.and, [u, v]⟩ := by
    have hg : gateAt C m = C.gates[m] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hm_len]
    rw [← hg, hgat_m]
  have hgku : C.gates[ku] = ⟨GateOp.or, [z, a]⟩ := by
    have hg : gateAt C ku = C.gates[ku] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hku_lt]
    rw [← hg, hgat_ku]
  have hgk : C.gates[k] = ⟨GateOp.or, [z, b]⟩ := by
    have hg : gateAt C k = C.gates[k] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hk_lt]
    rw [← hg, hgat_k]
  have hgnew_k : gs'[k] = ⟨GateOp.and, [a, b]⟩ := by
    dsimp [gs', gv]
    have hm_ne_k : m ≠ k := by omega
    simp [List.getElem_set, hlen, hm_ne_k]
  have hgnew_m : gs'[m] = ⟨GateOp.or, [z, v]⟩ := by
    dsimp [gs', gm]
    simp [List.getElem_set, hlen]
  have htake_k : gs'.take k = C.gates.take k := by
    have h1 : (C.gates.set k gv).take k = C.gates.take k :=
      take_set_self_of_le C.gates k k le_rfl gv
    have h2 : gs'.take k = (C.gates.set k gv).take k := by
      dsimp [gs']
      apply take_set_self_of_le
      omega
    rw [h2, h1]
  have hz_lt_ku : z < n + ku := by
    have hzin : z ∈ (gateAt C ku).inputs := by rw [hgat_ku]; simp
    exact hrb ku hku_lt z hzin
  have ha_lt_ku : a < n + ku := by
    have hain : a ∈ (gateAt C ku).inputs := by rw [hgat_ku]; simp
    exact hrb ku hku_lt a hain
  have hz_lt_k : z < n + k := by omega
  have ha_lt_k : a < n + k := by omega
  have hb_lt_k : b < n + k := by
    have hbin : b ∈ (gateAt C k).inputs := by rw [hgat_k]; simp
    exact hrb k hk_lt b hbin
  have hz_lt_m : z < n + m := by omega
  change ReadsBack n ⟨gs', C.output⟩ ∧ (⟨gs', C.output⟩ : Circuit).size = C.size ∧
    ∀ x : Fin n → Bool, (⟨gs', C.output⟩ : Circuit).eval (List.ofFn x) = C.eval (List.ofFn x)
  constructor
  · intro j hjlen i hi
    have hjlen_old : j < C.gates.length := by rw [← hlen]; exact hjlen
    by_cases hjk : j = k
    · subst j
      have hgj : gateAt ⟨gs', C.output⟩ k = ⟨GateOp.and, [a, b]⟩ := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hk_len']
        exact hgnew_k
      rw [hgj] at hi
      simp at hi
      rcases hi with hi | hi
      · subst i
        exact ha_lt_k
      · subst i
        exact hb_lt_k
    · by_cases hjm : j = m
      · subst j
        have hgj : gateAt ⟨gs', C.output⟩ m = ⟨GateOp.or, [z, v]⟩ := by
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hm_len']
          exact hgnew_m
        rw [hgj] at hi
        simp at hi
        rcases hi with hi | hi
        · subst i
          exact hz_lt_m
        · subst i
          exact hvn
      · have h1 : gateAt ⟨C.gates.set k gv, C.output⟩ j = gateAt C j := by
          exact gateAt_set_ne C.gates k j gv hk_lt hjlen_old hjk
        have h2 : gateAt ⟨gs', C.output⟩ j = gateAt ⟨C.gates.set k gv, C.output⟩ j := by
          dsimp [gs']
          exact gateAt_set_ne (C.gates.set k gv) m j gm (by simpa using hm_len)
            (by simpa using hjlen_old) hjm
        rw [h2, h1] at hi
        exact hrb j hjlen_old i hi
  constructor
  · simpa [Circuit.size] using hlen
  · intro x
    change (wf gs' (List.ofFn x)).getD C.output false = (wf C.gates (List.ofFn x)).getD C.output false
    let X : List Bool := List.ofFn x
    have hXlen : X.length = n := by simp [X]
    have hstable : ∀ t, t ≤ C.gates.length → ∀ w, w ≠ v → w < n + t →
        (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := by
      intro t
      induction t with
      | zero =>
          intro ht w hwne hwlt
          simp [wf, hXlen] at hwlt ⊢
      | succ t ih =>
          intro ht w hwne hwlt
          have htlt : t < C.gates.length := by omega
          have htlt' : t < gs'.length := by rw [hlen]; exact htlt
          have hlenold : (wf (C.gates.take t) X).length = n + t := by
            rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt htlt)]
          have hlennew : (wf (gs'.take t) X).length = n + t := by
            rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt htlt')]
          have iht : ∀ w, w ≠ v → w < n + t →
              (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := ih (by omega)
          have ihall : ∀ w, w ≠ v →
              (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := by
            intro w hwne
            by_cases hwlt' : w < n + t
            · exact iht w hwne hwlt'
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          by_cases htk : t = k
          · subst t
            rw [wf_take_succ C.gates k htlt X, wf_take_succ gs' k htlt' X]
            by_cases hwlt' : w < n + k
            · rw [snoc_lt_pref C.gates k htlt X _ w (by simpa [hXlen] using hwlt'),
                  snoc_lt_pref gs' k htlt' X _ w (by simpa [hXlen] using hwlt')]
              exact ihall w hwne
            · have hweq : w = n + k := by omega
              subst w
              exact False.elim (hwne hk_wire)
          · by_cases htm : t = m
            · subst t
              let A : Bool := (wf C.gates X).getD a false
              let Bv : Bool := (wf C.gates X).getD b false
              let Z : Bool := (wf C.gates X).getD z false
              have oldpref : ∀ (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w < n + j),
                  (wf (C.gates.take j) X).getD w false = (wf C.gates X).getD w false := by
                intro j hj w hw
                exact (wire_take C.gates X j w (by simpa [hXlen] using hw) (le_of_lt hj)).symm
              have newpref : ∀ (j : ℕ) (hj : j < gs'.length) (w : ℕ) (hw : w < n + j),
                  (wf (gs'.take j) X).getD w false = (wf gs' X).getD w false := by
                intro j hj w hw
                exact (wire_take gs' X j w (by simpa [hXlen] using hw) (le_of_lt hj)).symm
              have hu_full : (wf C.gates X).getD u false = GateOp.or.eval [Z, A] := by
                rw [wire_take C.gates X (ku + 1) u
                  (by simpa [hXlen] using (show u < n + (ku + 1) by omega)) (by omega)]
                rw [wf_take_succ C.gates ku hku_lt X]
                have hlenku : (wf (C.gates.take ku) X).length = n + ku := by
                  rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt hku_lt)]
                rw [← hku_wire, ← hlenku, getD_snoc_eq, hgku]
                have hzku : (wf (C.gates.take ku) X).getD z false = Z := by
                  dsimp [Z]
                  exact oldpref ku hku_lt z hz_lt_ku
                have haku : (wf (C.gates.take ku) X).getD a false = A := by
                  dsimp [A]
                  exact oldpref ku hku_lt a ha_lt_ku
                simp only [List.map_cons, List.map_nil]
                rw [hzku, haku]
              have hv_full : (wf C.gates X).getD v false = GateOp.or.eval [Z, Bv] := by
                rw [wire_take C.gates X (k + 1) v
                  (by simpa [hXlen] using (show v < n + (k + 1) by omega)) (by omega)]
                rw [wf_take_succ C.gates k hk_lt X]
                have hlenk : (wf (C.gates.take k) X).length = n + k := by
                  rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)]
                rw [← hk_wire, ← hlenk, getD_snoc_eq, hgk]
                have hzk : (wf (C.gates.take k) X).getD z false = Z := by
                  dsimp [Z]
                  exact oldpref k hk_lt z hz_lt_k
                have hbk : (wf (C.gates.take k) X).getD b false = Bv := by
                  dsimp [Bv]
                  exact oldpref k hk_lt b hb_lt_k
                simp only [List.map_cons, List.map_nil]
                rw [hzk, hbk]
              have hz_new_full : (wf gs' X).getD z false = Z := by
                rw [wire_take gs' X k z (by simpa [hXlen] using hz_lt_k) (le_of_lt hk_len')]
                rw [htake_k]
                dsimp [Z]
                exact oldpref k hk_lt z hz_lt_k
              have hv_new_full : (wf gs' X).getD v false = GateOp.and.eval [A, Bv] := by
                rw [wire_take gs' X (k + 1) v
                  (by simpa [hXlen] using (show v < n + (k + 1) by omega)) (by omega)]
                rw [wf_take_succ gs' k hk_len' X]
                have hlenk' : (wf (gs'.take k) X).length = n + k := by
                  rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt hk_len')]
                rw [← hk_wire, ← hlenk', getD_snoc_eq, hgnew_k]
                have hak : (wf (gs'.take k) X).getD a false = A := by
                  dsimp [A]
                  rw [htake_k]
                  exact oldpref k hk_lt a ha_lt_k
                have hbk : (wf (gs'.take k) X).getD b false = Bv := by
                  dsimp [Bv]
                  rw [htake_k]
                  exact oldpref k hk_lt b hb_lt_k
                simp only [List.map_cons, List.map_nil]
                rw [hak, hbk]
              have hu_m : (wf (C.gates.take m) X).getD u false = GateOp.or.eval [Z, A] := by
                rw [oldpref m hm_len u hu_lt_m, hu_full]
              have hv_m : (wf (C.gates.take m) X).getD v false = GateOp.or.eval [Z, Bv] := by
                rw [oldpref m hm_len v hvn, hv_full]
              have hz_m : (wf (gs'.take m) X).getD z false = Z := by
                rw [newpref m hm_len' z hz_lt_m, hz_new_full]
              have hv_m_new : (wf (gs'.take m) X).getD v false = GateOp.and.eval [A, Bv] := by
                rw [newpref m hm_len' v hvn, hv_new_full]
              have heval : C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) X).getD i false) =
                  gs'[m].op.eval (gs'[m].inputs.map fun i => (wf (gs'.take m) X).getD i false) := by
                rw [hgnew_m, hgm]
                simp only [List.map_cons, List.map_nil]
                rw [hu_m, hv_m, hz_m, hv_m_new]
                exact factor_ident Z A Bv
              rw [wf_take_succ C.gates m hm_len X, wf_take_succ gs' m hm_len' X]
              by_cases hwlt' : w < n + m
              · rw [snoc_lt_pref C.gates m hm_len X _ w (by simpa [hXlen] using hwlt'),
                    snoc_lt_pref gs' m hm_len' X _ w (by simpa [hXlen] using hwlt')]
                exact ihall w hwne
              · have hweq : w = n + m := by omega
                subst w
                conv_lhs => rw [← hlenold]
                conv_rhs => rw [← hlennew]
                rw [getD_snoc_eq, getD_snoc_eq]
                exact heval
            · have hreadt_v : v ∉ C.gates[t].inputs := by
                have hg : gateAt C t = C.gates[t] := by
                  unfold gateAt; rw [List.getD_eq_getElem _ _ htlt]
                rw [← hg]
                exact hread t htlt htm
              have hgt : gs'[t] = C.gates[t] := by
                dsimp [gs']
                have hm_ne_t : m ≠ t := by omega
                have hk_ne_t : k ≠ t := by omega
                simp [List.getElem_set, hlen, htk, htm, hm_ne_t, hk_ne_t]
              rw [wf_take_succ C.gates t htlt X, wf_take_succ gs' t htlt' X]
              have heval : C.gates[t].op.eval (C.gates[t].inputs.map fun i => (wf (C.gates.take t) X).getD i false) =
                  gs'[t].op.eval (gs'[t].inputs.map fun i => (wf (gs'.take t) X).getD i false) := by
                rw [hgt]
                congr 1
                apply List.map_congr_left
                intro i hi
                have hiv : i ≠ v := by intro h'; subst i; exact hreadt_v hi
                exact ihall i hiv
              rcases lt_trichotomy w (n + t) with hwlt | hweq | hwgt
              · rw [snoc_lt_pref C.gates t htlt X _ w (by simpa [hXlen] using hwlt),
                    snoc_lt_pref gs' t htlt' X _ w (by simpa [hXlen] using hwlt)]
                exact ihall w hwne
              · subst w
                conv_lhs => rw [← hlenold]
                conv_rhs => rw [← hlennew]
                rw [getD_snoc_eq, getD_snoc_eq]
                exact heval
              · rw [snoc_gt_pref C.gates t htlt X _ w (by simpa [hXlen] using hwgt),
                    snoc_gt_pref gs' t htlt' X _ w (by simpa [hXlen] using hwgt)]
    by_cases houtlt : C.output < n + C.gates.length
    · have ht := hstable C.gates.length le_rfl C.output hout houtlt
      rw [show gs'.take C.gates.length = gs' by rw [← hlen, List.take_length]] at ht
      simpa [X] using ht.symm
    · have hlenold : (wf C.gates X).length = n + C.gates.length := by rw [wf_len, hXlen]
      have hlennew : (wf gs' X).length = n + C.gates.length := by rw [wf_len, hXlen, hlen]
      have hfalse : (wf gs' X).getD C.output false = (wf C.gates X).getD C.output false := by
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simpa [X] using hfalse
