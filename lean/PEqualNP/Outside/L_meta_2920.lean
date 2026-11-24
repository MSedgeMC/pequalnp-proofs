import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

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

theorem bool_ident (op1 op2 : GateOp)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (A B C Z : Bool) :
    op1.eval [op2.eval [A, B], op1.eval [op2.eval [A, C], Z]] =
      op1.eval [op2.eval [A, op1.eval [B, C]], Z] := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases A <;> cases B <;> cases C <;> cases Z <;> simp [GateOp.eval]

theorem bool_ident_swap (op1 op2 : GateOp)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (A B C Z : Bool) :
    op1.eval [op1.eval [op2.eval [A, C], Z], op2.eval [A, B]] =
      op1.eval [op2.eval [A, op1.eval [B, C]], Z] := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases A <;> cases B <;> cases C <;> cases Z <;> simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2920

set_option maxHeartbeats 0 in
open PEqualNP.Outside.L_meta_2920 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hop his hiv hiw hj hisj hiviw hiwj ha_is hb_is ha_iv hb_iv
    hc_iv hz_iw hz_ne_iv hread_iv hread_iw hout_iv hout_iw
  let gs' : List Gate :=
    ((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j ⟨op1, [n + iw, z]⟩
  have hlen : gs'.length = C.gates.length := by simp [gs']
  have h_is_len : is < C.gates.length := by
    rcases List.getElem?_eq_some_iff.mp his with ⟨h, _⟩
    exact h
  have h_iv_len : iv < C.gates.length := by
    rcases List.getElem?_eq_some_iff.mp hiv with ⟨h, _⟩
    exact h
  have h_iw_len : iw < C.gates.length := by
    rcases List.getElem?_eq_some_iff.mp hiw with ⟨h, _⟩
    exact h
  have h_j_len : j < C.gates.length := by
    rcases hj with hj' | hj'
    · rcases List.getElem?_eq_some_iff.mp hj' with ⟨h, _⟩
      exact h
    · rcases List.getElem?_eq_some_iff.mp hj' with ⟨h, _⟩
      exact h
  have hj_get : C.gates[j] = ⟨op1, [n + is, n + iw]⟩ ∨ C.gates[j] = ⟨op1, [n + iw, n + is]⟩ := by
    rcases hj with hj' | hj'
    · left
      rcases List.getElem?_eq_some_iff.mp hj' with ⟨_, h⟩
      exact h
    · right
      rcases List.getElem?_eq_some_iff.mp hj' with ⟨_, h⟩
      exact h
  have h_is_len' : is < gs'.length := by rw [hlen]; exact h_is_len
  have h_iv_len' : iv < gs'.length := by rw [hlen]; exact h_iv_len
  have h_iw_len' : iw < gs'.length := by rw [hlen]; exact h_iw_len
  have h_j_len' : j < gs'.length := by rw [hlen]; exact h_j_len
  have his_get : C.gates[is] = ⟨op2, [a, b]⟩ := by
    rcases List.getElem?_eq_some_iff.mp his with ⟨_, h⟩
    exact h
  have hiv_get : C.gates[iv] = ⟨op2, [a, c]⟩ := by
    rcases List.getElem?_eq_some_iff.mp hiv with ⟨_, h⟩
    exact h
  have hiw_get : C.gates[iw] = ⟨op1, [n + iv, z]⟩ := by
    rcases List.getElem?_eq_some_iff.mp hiw with ⟨_, h⟩
    exact h
  have hj_mem : C.gates[j] ∈ C.gates := List.getElem_mem h_j_len
  have hj_some : C.gates[j]? = some C.gates[j] := by
    exact List.getElem?_eq_some_iff.mpr ⟨h_j_len, rfl⟩
  have hread_j_iv : n + iv ∉ C.gates[j].inputs := hread_iv j C.gates[j] hj_some (by omega)
  have hj_inputs_is : n + is ∈ C.gates[j].inputs := by
    rcases hj_get with hg | hg
    · rw [hg]; simp
    · rw [hg]; simp
  have his_ne_iv : is ≠ iv := by
    intro h
    subst is
    exact hread_j_iv hj_inputs_is
  have his_ne_iw : is ≠ iw := by
    intro h
    have hsome : (some ⟨op2, [a, b]⟩ : Option Gate) = some ⟨op1, [n + iv, z]⟩ := by
      rw [← his, ← hiw, h]
    have hg : (⟨op2, [a, b]⟩ : Gate) = ⟨op1, [n + iv, z]⟩ := Option.some.inj hsome
    have hins : [a, b] = [n + iv, z] := congrArg Gate.inputs hg
    simp at hins
    omega
  have hz_ne_iw : z ≠ n + iw := by omega
  have ha_ne_iv : a ≠ n + iv := by omega
  have ha_ne_iw : a ≠ n + iw := by omega
  have hb_ne_iv : b ≠ n + iv := by omega
  have hb_ne_iw : b ≠ n + iw := by omega
  have hc_ne_iv : c ≠ n + iv := by omega
  have hc_ne_iw : c ≠ n + iw := by omega
  have htake_iv : gs'.take iv = C.gates.take iv := by
    have h1 : (C.gates.set iv ⟨op1, [b, c]⟩).take iv = C.gates.take iv :=
      take_set_self_of_le C.gates iv iv le_rfl ⟨op1, [b, c]⟩
    have h2 : ((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).take iv =
        (C.gates.set iv ⟨op1, [b, c]⟩).take iv :=
      take_set_self_of_le (C.gates.set iv ⟨op1, [b, c]⟩) iw iv (le_of_lt hiviw) ⟨op2, [a, n + iv]⟩
    have h3 : gs'.take iv = ((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).take iv := by
      dsimp [gs']
      apply take_set_self_of_le
      omega
    rw [h3, h2, h1]
  constructor
  · funext x
    change (wf gs' (List.ofFn x)).getD C.output false = (wf C.gates (List.ofFn x)).getD C.output false
    let X : List Bool := List.ofFn x
    have hXlen : X.length = n := by simp [X]
    have hstable : ∀ t, t ≤ C.gates.length → ∀ w, w ∉ [n + iv, n + iw] → w < n + t →
        (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := by
      intro t
      induction t with
      | zero =>
          intro ht w hwB hwlt
          simp [wf, hXlen] at hwlt ⊢
      | succ t ih =>
          intro ht w hwB hwlt
          have htlt : t < C.gates.length := by omega
          have htlt' : t < gs'.length := by rw [hlen]; exact htlt
          have iht : ∀ w, w ∉ [n + iv, n + iw] → w < n + t →
              (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := ih (by omega)
          have hlenold : (wf (C.gates.take t) X).length = n + t := by
            rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt htlt)]
          have hlennew : (wf (gs'.take t) X).length = n + t := by
            rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt htlt')]
          have ihall : ∀ w, w ∉ [n + iv, n + iw] →
              (wf (C.gates.take t) X).getD w false = (wf (gs'.take t) X).getD w false := by
            intro w hwB'
            by_cases hwlt' : w < n + t
            · exact iht w hwB' hwlt'
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          by_cases htiv : t = iv
          · subst t
            have hwiv : w < n + iv := by
              have hne : w ≠ n + iv := by
                intro h'
                exact hwB (by simp [h'])
              omega
            rw [wf_take_succ C.gates iv htlt X, wf_take_succ gs' iv htlt' X]
            rw [snoc_lt_pref C.gates iv htlt X _ w (by simpa [hXlen] using hwiv),
                snoc_lt_pref gs' iv htlt' X _ w (by simpa [hXlen] using hwiv)]
            exact ihall w hwB
          · by_cases htiw : t = iw
            · subst t
              have hwiw : w < n + iw := by
                have hne : w ≠ n + iw := by
                  intro h'
                  exact hwB (by simp [h'])
                omega
              rw [wf_take_succ C.gates iw htlt X, wf_take_succ gs' iw htlt' X]
              rw [snoc_lt_pref C.gates iw htlt X _ w (by simpa [hXlen] using hwiw),
                  snoc_lt_pref gs' iw htlt' X _ w (by simpa [hXlen] using hwiw)]
              exact ihall w hwB
            · by_cases htj : t = j
              · subst t
                have hA : w ∉ [n + iv, n + iw] := hwB
                have hfull : ∀ v, v ∉ [n + iv, n + iw] → v < n + j →
                    (wf gs' X).getD v false = (wf C.gates X).getD v false := by
                  intro v hvB hvlt
                  rw [wire_take gs' X j v (by simpa [hXlen] using hvlt) (le_of_lt h_j_len')]
                  rw [← ihall v hvB]
                  rw [← wire_take C.gates X j v (by simpa [hXlen] using hvlt) (le_of_lt h_j_len)]
                let A : Bool := (wf C.gates X).getD a false
                let Bv : Bool := (wf C.gates X).getD b false
                let Cb : Bool := (wf C.gates X).getD c false
                let Z : Bool := (wf C.gates X).getD z false
                have oldpref : ∀ (k : ℕ) (hk : k < C.gates.length) (v : ℕ) (hv : v < n + k),
                    (wf (C.gates.take k) X).getD v false = (wf C.gates X).getD v false := by
                  intro k hk v hv
                  exact (wire_take C.gates X k v (by simpa [hXlen] using hv) (le_of_lt hk)).symm
                have newpref : ∀ (k : ℕ) (hk : k < gs'.length) (v : ℕ) (hv : v < n + k)
                    (hvB : v ∉ [n + iv, n + iw]) (hvj : v < n + j),
                    (wf (gs'.take k) X).getD v false = (wf C.gates X).getD v false := by
                  intro k hk v hv hvB hvj
                  rw [← wire_take gs' X k v (by simpa [hXlen] using hv) (le_of_lt hk)]
                  exact hfull v hvB hvj
                have hIs_old : (wf (C.gates.take j) X).getD (n + is) false = op2.eval [A, Bv] := by
                  rw [← wire_take C.gates X j (n + is) (by simpa [hXlen] using (show n + is < n + j by omega)) (le_of_lt h_j_len)]
                  rw [wire_take C.gates X (is + 1) (n + is) (by simpa [hXlen] using (show n + is < n + (is + 1) by omega)) (by omega)]
                  rw [wf_take_succ C.gates is h_is_len X]
                  have hlenis : (wf (C.gates.take is) X).length = n + is := by
                    rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt h_is_len)]
                  rw [← hlenis, getD_snoc_eq, his_get]
                  have haa : (wf (C.gates.take is) X).getD a false = A := by
                    dsimp [A]; exact oldpref is h_is_len a ha_is
                  have hbb : (wf (C.gates.take is) X).getD b false = Bv := by
                    dsimp [Bv]; exact oldpref is h_is_len b hb_is
                  simp only [List.map_cons, List.map_nil]
                  rw [haa, hbb]
                have hIs_new : (wf (gs'.take j) X).getD (n + is) false = op2.eval [A, Bv] := by
                  rw [← hIs_old]
                  rw [← wire_take gs' X j (n + is) (by simpa [hXlen] using (show n + is < n + j by omega)) (le_of_lt h_j_len')]
                  rw [← wire_take C.gates X j (n + is) (by simpa [hXlen] using (show n + is < n + j by omega)) (le_of_lt h_j_len)]
                  exact hfull (n + is) (by simp [his_ne_iv, his_ne_iw]) (by omega)
                have hIv_old : (wf (C.gates.take iw) X).getD (n + iv) false = op2.eval [A, Cb] := by
                  rw [← wire_take C.gates X iw (n + iv) (by simpa [hXlen] using (show n + iv < n + iw by omega)) (le_of_lt h_iw_len)]
                  rw [wire_take C.gates X (iv + 1) (n + iv) (by simpa [hXlen] using (show n + iv < n + (iv + 1) by omega)) (by omega)]
                  rw [wf_take_succ C.gates iv h_iv_len X]
                  have hleniv : (wf (C.gates.take iv) X).length = n + iv := by
                    rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt h_iv_len)]
                  rw [← hleniv, getD_snoc_eq, hiv_get]
                  have haa : (wf (C.gates.take iv) X).getD a false = A := by
                    dsimp [A]; exact oldpref iv h_iv_len a ha_iv
                  have hcc : (wf (C.gates.take iv) X).getD c false = Cb := by
                    dsimp [Cb]; exact oldpref iv h_iv_len c hc_iv
                  simp only [List.map_cons, List.map_nil]
                  rw [haa, hcc]
                have hgsiv : gs'[iv] = ⟨op1, [b, c]⟩ := by
                  dsimp [gs']
                  have hj_ne_iv : j ≠ iv := by omega
                  have hiw_ne_iv : iw ≠ iv := by omega
                  simp [List.getElem_set, hlen, hj_ne_iv, hiw_ne_iv]
                have hIv_new : (wf (gs'.take iw) X).getD (n + iv) false = op1.eval [Bv, Cb] := by
                  rw [← wire_take gs' X iw (n + iv) (by simpa [hXlen] using (show n + iv < n + iw by omega)) (le_of_lt h_iw_len')]
                  rw [wire_take gs' X (iv + 1) (n + iv) (by simpa [hXlen] using (show n + iv < n + (iv + 1) by omega)) (by omega)]
                  rw [wf_take_succ gs' iv h_iv_len' X]
                  have hleniv' : (wf (gs'.take iv) X).length = n + iv := by
                    rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt h_iv_len')]
                  rw [← hleniv', getD_snoc_eq, hgsiv]
                  have hbb : (wf (gs'.take iv) X).getD b false = Bv := by
                    dsimp [Bv]
                    rw [htake_iv]
                    exact oldpref iv h_iv_len b hb_iv
                  have hcc : (wf (gs'.take iv) X).getD c false = Cb := by
                    dsimp [Cb]
                    rw [htake_iv]
                    exact oldpref iv h_iv_len c hc_iv
                  simp only [List.map_cons, List.map_nil]
                  rw [hbb, hcc]
                have hIw_old : (wf (C.gates.take j) X).getD (n + iw) false = op1.eval [op2.eval [A, Cb], Z] := by
                  rw [← wire_take C.gates X j (n + iw) (by simpa [hXlen] using (show n + iw < n + j by omega)) (le_of_lt h_j_len)]
                  rw [wire_take C.gates X (iw + 1) (n + iw) (by simpa [hXlen] using (show n + iw < n + (iw + 1) by omega)) (by omega)]
                  rw [wf_take_succ C.gates iw h_iw_len X]
                  have hleniw : (wf (C.gates.take iw) X).length = n + iw := by
                    rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt h_iw_len)]
                  rw [← hleniw, getD_snoc_eq, hiw_get]
                  have hzz : (wf (C.gates.take iw) X).getD z false = Z := by
                    dsimp [Z]; exact oldpref iw h_iw_len z hz_iw
                  simp only [List.map_cons, List.map_nil]
                  rw [hIv_old, hzz]
                have hgsiv' : gs'[iw] = ⟨op2, [a, n + iv]⟩ := by
                  dsimp [gs']
                  have hj_ne_iw : j ≠ iw := by omega
                  have hiv_ne_iw : iv ≠ iw := by omega
                  simp [List.getElem_set, hlen, hj_ne_iw, hiv_ne_iw]
                have hIw_new : (wf (gs'.take j) X).getD (n + iw) false = op2.eval [A, op1.eval [Bv, Cb]] := by
                  rw [← wire_take gs' X j (n + iw) (by simpa [hXlen] using (show n + iw < n + j by omega)) (le_of_lt h_j_len')]
                  rw [wire_take gs' X (iw + 1) (n + iw) (by simpa [hXlen] using (show n + iw < n + (iw + 1) by omega)) (by omega)]
                  rw [wf_take_succ gs' iw h_iw_len' X]
                  have hleniw' : (wf (gs'.take iw) X).length = n + iw := by
                    rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt h_iw_len')]
                  rw [← hleniw', getD_snoc_eq, hgsiv']
                  have haa : (wf (gs'.take iw) X).getD a false = A := by
                    dsimp [A]
                    exact newpref iw h_iw_len' a (by omega) (by simp [ha_ne_iv, ha_ne_iw]) (by omega)
                  simp only [List.map_cons, List.map_nil]
                  rw [haa, hIv_new]
                have hZ_new : (wf (gs'.take j) X).getD z false = Z := by
                  dsimp [Z]
                  exact newpref j h_j_len' z (by omega) (by simp [hz_ne_iv, hz_ne_iw]) (by omega)
                have hgsj : gs'[j] = ⟨op1, [n + iw, z]⟩ := by
                  dsimp [gs']
                  simp [List.getElem_set, hlen]
                have heval : C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wf (C.gates.take j) X).getD i false) =
                    gs'[j].op.eval (gs'[j].inputs.map fun i => (wf (gs'.take j) X).getD i false) := by
                  rw [hgsj]
                  rcases hj with hj' | hj'
                  · rcases List.getElem?_eq_some_iff.mp hj' with ⟨_, hgj⟩
                    rw [hgj]
                    simp only [List.map_cons, List.map_nil]
                    rw [hIs_old, hIw_old, hIw_new, hZ_new]
                    exact bool_ident op1 op2 hop A Bv Cb Z
                  · rcases List.getElem?_eq_some_iff.mp hj' with ⟨_, hgj⟩
                    rw [hgj]
                    simp only [List.map_cons, List.map_nil]
                    rw [hIw_old, hIs_old, hIw_new, hZ_new]
                    exact bool_ident_swap op1 op2 hop A Bv Cb Z
                rw [wf_take_succ C.gates j h_j_len X, wf_take_succ gs' j h_j_len' X]
                rcases lt_trichotomy w (n + j) with hwlt | hweq | hwgt
                · rw [snoc_lt_pref C.gates j h_j_len X _ w (by simpa [hXlen] using hwlt),
                      snoc_lt_pref gs' j h_j_len' X _ w (by simpa [hXlen] using hwlt)]
                  exact ihall w hwB
                · subst w
                  conv_lhs => rw [← hlenold]
                  conv_rhs => rw [← hlennew]
                  rw [getD_snoc_eq, getD_snoc_eq]
                  exact heval
                · rw [snoc_gt_pref C.gates j h_j_len X _ w (by simpa [hXlen] using hwgt),
                      snoc_gt_pref gs' j h_j_len' X _ w (by simpa [hXlen] using hwgt)]
              · have hmemt : C.gates[t] ∈ C.gates := List.getElem_mem htlt
                have hreadt_iv : n + iv ∉ C.gates[t].inputs := by
                  have hs : C.gates[t]? = some C.gates[t] := List.getElem?_eq_some_iff.mpr ⟨htlt, rfl⟩
                  exact hread_iv t C.gates[t] hs htiw
                have hreadt_iw : n + iw ∉ C.gates[t].inputs := by
                  have hs : C.gates[t]? = some C.gates[t] := List.getElem?_eq_some_iff.mpr ⟨htlt, rfl⟩
                  exact hread_iw t C.gates[t] hs htj
                have hgt : gs'[t] = C.gates[t] := by
                  dsimp [gs']
                  have hj_ne_t : j ≠ t := by omega
                  have hiw_ne_t : iw ≠ t := by omega
                  have hiv_ne_t : iv ≠ t := by omega
                  simp [List.getElem_set, htiv, htiw, htj, hlen, hj_ne_t, hiw_ne_t, hiv_ne_t]
                rw [wf_take_succ C.gates t htlt X, wf_take_succ gs' t htlt' X]
                have heval : C.gates[t].op.eval (C.gates[t].inputs.map fun i => (wf (C.gates.take t) X).getD i false) =
                    gs'[t].op.eval (gs'[t].inputs.map fun i => (wf (gs'.take t) X).getD i false) := by
                  rw [hgt]
                  congr 1
                  apply List.map_congr_left
                  intro i hi
                  have hiiv : i ≠ n + iv := by intro h'; subst i; exact hreadt_iv hi
                  have hiiw : i ≠ n + iw := by intro h'; subst i; exact hreadt_iw hi
                  exact ihall i (by simp [hiiv, hiiw])
                rcases lt_trichotomy w (n + t) with hwlt | hweq | hwgt
                · rw [snoc_lt_pref C.gates t htlt X _ w (by simpa [hXlen] using hwlt),
                      snoc_lt_pref gs' t htlt' X _ w (by simpa [hXlen] using hwlt)]
                  exact ihall w hwB
                · subst w
                  conv_lhs => rw [← hlenold]
                  conv_rhs => rw [← hlennew]
                  rw [getD_snoc_eq, getD_snoc_eq]
                  exact heval
                · rw [snoc_gt_pref C.gates t htlt X _ w (by simpa [hXlen] using hwgt),
                      snoc_gt_pref gs' t htlt' X _ w (by simpa [hXlen] using hwgt)]
    by_cases houtlt : C.output < n + C.gates.length
    · have ht := hstable C.gates.length le_rfl C.output (by simp [hout_iv, hout_iw]) houtlt
      rw [show gs'.take C.gates.length = gs' by rw [← hlen, List.take_length]] at ht
      simpa [X] using ht.symm
    · have hlenold : (wf C.gates X).length = n + C.gates.length := by rw [wf_len, hXlen]
      have hlennew : (wf gs' X).length = n + C.gates.length := by rw [wf_len, hXlen, hlen]
      have hfalse : (wf gs' X).getD C.output false = (wf C.gates X).getD C.output false := by
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simpa [X] using hfalse
  · simp [gs']
