import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_273

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma stepWire_length (w : List Bool) (g : Gate) :
    (stepWire w g).length = w.length + 1 := by
  simp [stepWire]

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      calc
        ((g :: gs).foldl stepWire w).length = (gs.foldl stepWire (stepWire w g)).length := by simp
        _ = (stepWire w g).length + gs.length := ih (stepWire w g)
        _ = w.length + 1 + gs.length := by rw [stepWire_length]
        _ = w.length + (g :: gs).length := by simp; omega

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      have hi' : i < (stepWire w g).length := by
        rw [stepWire_length]
        omega
      rw [ih (stepWire w g) hi']
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append, hi]

private lemma foldl_getD_at (gs : List Gate) (x : List Bool) (t : ℕ) (ht : t < gs.length) :
    (gs.foldl stepWire x).getD (x.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        if i < x.length + t then (gs.foldl stepWire x).getD i false else false) := by
  induction gs generalizing x t with
  | nil => simp at ht
  | cons g gs ih =>
      cases t with
      | zero =>
          simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
          have hlen : (stepWire x g).length = x.length + 1 := stepWire_length x g
          have hpref (i : ℕ) (hi : i < x.length) :
              (gs.foldl stepWire (stepWire x g)).getD i false = x.getD i false := by
            rw [getD_prefix gs (stepWire x g) i]
            · simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append, hi]
            · rw [hlen]
              omega
          have hval : (stepWire x g).getD x.length false =
              g.op.eval (g.inputs.map fun i => x.getD i false) := by
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append]
          rw [show (gs.foldl stepWire (stepWire x g)).getD x.length false =
              (stepWire x g).getD x.length false by
            rw [getD_prefix gs (stepWire x g) x.length]
            rw [hlen]
            omega]
          rw [hval]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hix : i < x.length
          · rw [if_pos hix, hpref i hix]
          · rw [if_neg hix]
            exact getD_ge_length x i (Nat.le_of_not_gt hix)
      | succ t =>
          have ht' : t < gs.length := by simpa using ht
          simp only [List.foldl_cons]
          have hih := ih (stepWire x g) t ht'
          rw [show x.length + (t + 1) = x.length + 1 + t by omega]
          simpa [stepWire, List.length_append, List.length_cons, List.length_nil] using hih

private lemma wires_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires x).getD (x.length + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < x.length + t then (C.wires x).getD i false else false) := by
  rw [Circuit.wires]
  change (C.gates.foldl stepWire x).getD (x.length + t) false =
    (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
      if i < x.length + t then (C.gates.foldl stepWire x).getD i false else false)
  exact foldl_getD_at C.gates x t ht

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private def sing (p : Fin 6) : Fin 6 → Bool := fun q => decide (q = p)

private def Ls (C : Circuit) (w : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun p => (C.wires (List.ofFn (sing p))).getD w false = true)

private lemma mem_Ls (C : Circuit) (w : ℕ) (p : Fin 6) :
    p ∈ Ls C w ↔ (C.wires (List.ofFn (sing p))).getD w false = true := by
  simp [Ls]

private lemma Ls_input (C : Circuit) (w : ℕ) (hw : w < 6) :
    Ls C w = {⟨w, hw⟩} := by
  ext p
  rw [mem_Ls]
  change (C.gates.foldl stepWire (List.ofFn (sing p))).getD w false = true ↔
    p ∈ ({(⟨w, hw⟩ : Fin 6)} : Finset (Fin 6))
  rw [getD_prefix C.gates (List.ofFn (sing p)) w (by simpa using hw)]
  rw [getD_ofFn (sing p) w hw]
  simp [sing, eq_comm]

private lemma wires_length (C : Circuit) (x : Fin 6 → Bool) :
    (C.wires (List.ofFn x)).length = 6 + C.size := by
  change (C.gates.foldl stepWire (List.ofFn x)).length = 6 + C.gates.length
  rw [foldl_stepWire_length]
  simp

private lemma Ls_out (C : Circuit) (w : ℕ) (hw : 6 + C.size ≤ w) :
    Ls C w = ∅ := by
  ext p
  rw [mem_Ls]
  have hfalse : (C.wires (List.ofFn (sing p))).getD w false = false := by
    apply getD_ge_length
    rw [wires_length C (sing p)]
    exact hw
  rw [hfalse]
  simp

private lemma Ls_gate_or (C : Circuit) (t : ℕ) (ht : t < C.gates.length) (a b : ℕ)
    (hab : (C.gates[t]).inputs = [a, b]) (hop : (C.gates[t]).op = GateOp.or) :
    Ls C (6 + t) =
      (if a < 6 + t then Ls C a else ∅) ∪ (if b < 6 + t then Ls C b else ∅) := by
  ext p
  have hwg := wires_gate C (List.ofFn (sing p)) t ht
  have hwg' : (C.wires (List.ofFn (sing p))).getD (6 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < 6 + t then (C.wires (List.ofFn (sing p))).getD i false else false) := by
    simpa using hwg
  rw [mem_Ls, hwg']
  by_cases ha : a < 6 + t <;> by_cases hb : b < 6 + t <;>
    simp [hop, hab, mem_Ls, GateOp.eval, ha, hb]

private lemma Ls_gate_and (C : Circuit) (t : ℕ) (ht : t < C.gates.length) (a b : ℕ)
    (hab : (C.gates[t]).inputs = [a, b]) (hand : (C.gates[t]).op = GateOp.and) :
    Ls C (6 + t) =
      (if a < 6 + t then Ls C a else ∅) ∩ (if b < 6 + t then Ls C b else ∅) := by
  ext p
  have hwg := wires_gate C (List.ofFn (sing p)) t ht
  have hwg' : (C.wires (List.ofFn (sing p))).getD (6 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < 6 + t then (C.wires (List.ofFn (sing p))).getD i false else false) := by
    simpa using hwg
  rw [mem_Ls, hwg']
  by_cases ha : a < 6 + t <;> by_cases hb : b < 6 + t <;>
    simp [hand, hab, mem_Ls, GateOp.eval, ha, hb]

private lemma wires_mono_aux (gs : List Gate)
    (hall : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (wx wy : List Bool) (hlen : wx.length = wy.length)
    (hle : ∀ i, wx.getD i false = true → wy.getD i false = true) :
    ∀ i, (gs.foldl stepWire wx).getD i false = true → (gs.foldl stepWire wy).getD i false = true := by
  induction gs generalizing wx wy with
  | nil => simpa
  | cons g gs ih =>
      have hg := hall g (by simp)
      obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
        match hli : g.inputs with
        | [] => simp [hli] at hg
        | [u] => simp [hli] at hg
        | u :: v :: [] => exact ⟨u, v, by simp [hli]⟩
        | u :: v :: w :: ws => simp [hli] at hg
      simp only [List.foldl_cons]
      have hlen' : (stepWire wx g).length = (stepWire wy g).length := by
        simp [stepWire, hlen]
      have hle' : ∀ i, (stepWire wx g).getD i false = true → (stepWire wy g).getD i false = true := by
        intro i hi
        by_cases hil : i < wx.length
        · have hix : wx.getD i false = true := by
            simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append, hil] using hi
          have hiy := hle i hix
          have hily : i < wy.length := by omega
          simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append, hily] using hiy
        · by_cases hieq : i = wx.length
          · subst i
            have hvalx : g.op.eval (g.inputs.map fun j => wx.getD j false) = true := by
              simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append] using hi
            have hvaly : g.op.eval (g.inputs.map fun j => wy.getD j false) = true := by
              rcases hg.1 with hand | hor
              · rw [hand] at hvalx ⊢
                simp [GateOp.eval, hab] at hvalx ⊢
                exact ⟨hle a hvalx.1, hle b hvalx.2⟩
              · rw [hor] at hvalx ⊢
                simp [GateOp.eval, hab] at hvalx ⊢
                rcases hvalx with ha | hb
                · exact Or.inl (hle a ha)
                · exact Or.inr (hle b hb)
            simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append, hlen] using hvaly
          · have hgt : wx.length + 1 ≤ i := by omega
            have hfalse : (stepWire wx g).getD i false = false :=
              getD_ge_length (stepWire wx g) i (by simp [stepWire_length]; omega)
            have hi' : (stepWire wx g).getD i false = true := by
              simpa [List.getD_eq_getElem?_getD] using hi
            rw [hfalse] at hi'
            contradiction
      exact ih (by intro g' hg'; exact hall g' (by simp [hg'])) (stepWire wx g) (stepWire wy g) hlen' hle'

private lemma wires_mono (C : Circuit)
    (hall : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin 6 → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  apply wires_mono_aux C.gates hall (List.ofFn x) (List.ofFn y)
  · simp
  · intro i hi
    by_cases hlt : i < 6
    · have hix0 := hi
      rw [getD_ofFn x i hlt] at hix0
      have hiy := hxy ⟨i, hlt⟩ hix0
      rw [getD_ofFn y i hlt]
      exact hiy
    · have hfalse : (List.ofFn x).getD i false = false :=
        getD_ge_length (List.ofFn x) i (by simpa using hlt)
      have hi' : (List.ofFn x).getD i false = true := by
        simpa [List.getD_eq_getElem?_getD] using hi
      rw [hfalse] at hi'
      contradiction

private def S : Fin 3 → Finset (Fin 6) := ![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}]

private lemma S_card (i : Fin 3) : (S i).card = 3 := by
  fin_cases i <;> decide

private lemma S_inter_card (i j : Fin 3) (hij : i ≠ j) : (S i ∩ S j).card = 1 := by
  fin_cases i <;> fin_cases j <;> simp at hij <;> decide

end PEqualNP.Outside.L_meta_273

open PEqualNP.Outside.L_meta_273
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ),
  C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  intro h
  classical
  rcases h with ⟨C, o, hsize, hall, hcond⟩
  let n := C.size
  have two_gates (i : Fin 3) :
      ∃ k₁ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧ k₁ ≠ k₂ ∧
        Ls C (6 + k₁) ⊆ S i ∧ 2 ≤ (Ls C (6 + k₁)).card ∧
        Ls C (6 + k₂) ⊆ S i ∧ 2 ≤ (Ls C (6 + k₂)).card := by
    have hLout : Ls C (o i) = S i := by
      ext p
      rw [mem_Ls]
      exact (hcond i).1 p
    have hcardout : (Ls C (o i)).card = 3 := by
      rw [hLout]
      exact S_card i
    have ho_ge : 6 ≤ o i := by
      by_contra hlt
      have hw : o i < 6 := by omega
      rw [Ls_input C (o i) hw] at hcardout
      simp at hcardout
    have ho_lt : o i < 6 + n := by
      by_contra hlt
      have hw : 6 + n ≤ o i := by omega
      rw [Ls_out C (o i) hw] at hcardout
      simp at hcardout
    let kt := o i - 6
    have hkt : kt < n := by omega
    have hokt : o i = 6 + kt := by omega
    have hLg : Ls C (6 + kt) = S i := by simpa [hokt] using hLout
    have hgmem : C.gates[kt] ∈ C.gates := List.getElem_mem ..
    have hg := hall C.gates[kt] hgmem
    obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[kt]).inputs = [a, b] := by
      match hli : (C.gates[kt]).inputs with
      | [] => simp [hli] at hg
      | [u] => simp [hli] at hg
      | u :: v :: [] => exact ⟨u, v, by simp [hli]⟩
      | u :: v :: w :: ws => simp [hli] at hg
    by_cases hop : C.gates[kt].op = GateOp.or
    · have hcomp : Ls C (6 + kt) =
          (if a < 6 + kt then Ls C a else ∅) ∪ (if b < 6 + kt then Ls C b else ∅) :=
        Ls_gate_or C kt hkt a b hab hop
      have hU : (if a < 6 + kt then Ls C a else ∅) ∪ (if b < 6 + kt then Ls C b else ∅) = S i := by
        rw [← hcomp]
        exact hLg
      have hsuba : (if a < 6 + kt then Ls C a else ∅) ⊆ S i := by
        intro p hp
        have : p ∈ (if a < 6 + kt then Ls C a else ∅) ∪ (if b < 6 + kt then Ls C b else ∅) :=
          Finset.mem_union.mpr (Or.inl hp)
        simpa [hU] using this
      have hsubb : (if b < 6 + kt then Ls C b else ∅) ⊆ S i := by
        intro p hp
        have : p ∈ (if a < 6 + kt then Ls C a else ∅) ∪ (if b < 6 + kt then Ls C b else ∅) :=
          Finset.mem_union.mpr (Or.inr hp)
        simpa [hU] using this
      have hcarda : 2 ≤ (if a < 6 + kt then Ls C a else ∅).card ∨
          2 ≤ (if b < 6 + kt then Ls C b else ∅).card := by
        by_contra hn
        push_neg at hn
        have hle := Finset.card_union_le (if a < 6 + kt then Ls C a else ∅) (if b < 6 + kt then Ls C b else ∅)
        rw [hU, S_card i] at hle
        omega
      rcases hcarda with hca | hcb
      · have ha_lt : a < 6 + kt := by
          by_contra ha
          have hzero : (if a < 6 + kt then Ls C a else (∅ : Finset (Fin 6))) = ∅ := by simp [ha]
          rw [hzero] at hca
          simp at hca
        let k₂ := a - 6
        have ha_ge : 6 ≤ a := by
          by_contra ha
          have halt : a < 6 := by omega
          have hone : (if a < 6 + kt then Ls C a else (∅ : Finset (Fin 6))) = {⟨a, halt⟩} := by
            simp [ha_lt, Ls_input C a halt]
          rw [hone] at hca
          simp at hca
        have haeq : a = 6 + k₂ := by omega
        refine ⟨kt, k₂, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hLg]
        · rw [hLg, S_card i]
          omega
        · have hk₂lt : k₂ < kt := by omega
          simpa [haeq, hk₂lt] using hsuba
        · have hk₂lt : k₂ < kt := by omega
          simpa [haeq, hk₂lt] using hca
      · have hb_lt : b < 6 + kt := by
          by_contra hb
          have hzero : (if b < 6 + kt then Ls C b else (∅ : Finset (Fin 6))) = ∅ := by simp [hb]
          rw [hzero] at hcb
          simp at hcb
        let k₂ := b - 6
        have hb_ge : 6 ≤ b := by
          by_contra hb
          have hblt : b < 6 := by omega
          have hone : (if b < 6 + kt then Ls C b else (∅ : Finset (Fin 6))) = {⟨b, hblt⟩} := by
            simp [hb_lt, Ls_input C b hblt]
          rw [hone] at hcb
          simp at hcb
        have hbeq : b = 6 + k₂ := by omega
        refine ⟨kt, k₂, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hLg]
        · rw [hLg, S_card i]
          omega
        · have hk₂lt : k₂ < kt := by omega
          simpa [hbeq, hk₂lt] using hsubb
        · have hk₂lt : k₂ < kt := by omega
          simpa [hbeq, hk₂lt] using hcb
    · have hand : C.gates[kt].op = GateOp.and := by
        rcases hg.1 with h | h
        · exact h
        · contradiction
      have hcomp : Ls C (6 + kt) =
          (if a < 6 + kt then Ls C a else ∅) ∩ (if b < 6 + kt then Ls C b else ∅) :=
        Ls_gate_and C kt hkt a b hab hand
      let A := if a < 6 + kt then Ls C a else ∅
      let B := if b < 6 + kt then Ls C b else ∅
      have hAB : A ∩ B = S i := by
        rw [← hcomp]
        exact hLg
      have hSA : S i ⊆ A := by
        intro p hp
        have : p ∈ A ∩ B := by rw [hAB]; exact hp
        exact (Finset.mem_inter.mp this).1
      have hSB : S i ⊆ B := by
        intro p hp
        have : p ∈ A ∩ B := by rw [hAB]; exact hp
        exact (Finset.mem_inter.mp this).2
      have hAeq : A = S i ∨ B = S i := by
        by_contra hne
        push_neg at hne
        rcases hne with ⟨hAneq, hBneq⟩
        have hAstrict : ∃ p, p ∈ A ∧ p ∉ S i := by
          by_contra hn
          push_neg at hn
          apply hAneq
          exact Finset.Subset.antisymm hn hSA
        have hBstrict : ∃ q, q ∈ B ∧ q ∉ S i := by
          by_contra hn
          push_neg at hn
          apply hBneq
          exact Finset.Subset.antisymm hn hSB
        rcases hAstrict with ⟨p, hpA, hpS⟩
        rcases hBstrict with ⟨q, hqB, hqS⟩
        have ha_lt : a < 6 + kt := by
          by_contra ha
          have hz : A = (∅ : Finset (Fin 6)) := by simp [A, ha]
          rw [hz] at hpA
          simp at hpA
        have hb_lt : b < 6 + kt := by
          by_contra hb
          have hz : B = (∅ : Finset (Fin 6)) := by simp [B, hb]
          rw [hz] at hqB
          simp at hqB
        have hpa : (C.wires (List.ofFn (sing p))).getD a false = true := by
          simpa [A, ha_lt, mem_Ls] using hpA
        have hqb : (C.wires (List.ofFn (sing q))).getD b false = true := by
          simpa [B, hb_lt, mem_Ls] using hqB
        let x : Fin 6 → Bool := fun r => decide (r = p ∨ r = q)
        have hxa : x p = true := by simp [x]
        have hxb : x q = true := by simp [x]
        have hap : (C.wires (List.ofFn x)).getD a false = true :=
          wires_mono C hall (sing p) x (by intro r hr; simp [sing] at hr; subst r; exact hxa) a hpa
        have hbq : (C.wires (List.ofFn x)).getD b false = true :=
          wires_mono C hall (sing q) x (by intro r hr; simp [sing] at hr; subst r; exact hxb) b hqb
        have hval : (C.wires (List.ofFn x)).getD (6 + kt) false = true := by
          have hwg := wires_gate C (List.ofFn x) kt hkt
          have hwg' : (C.wires (List.ofFn x)).getD (6 + kt) false =
              (C.gates[kt]).op.eval ((C.gates[kt]).inputs.map fun i =>
                if i < 6 + kt then (C.wires (List.ofFn x)).getD i false else false) := by
            simpa using hwg
          rw [hwg', hand]
          simp [GateOp.eval, hab, ha_lt, hb_lt]
          constructor
          · simpa [List.getD_eq_getElem?_getD] using hap
          · simpa [List.getD_eq_getElem?_getD] using hbq
        have hcardx : (Finset.univ.filter (fun r : Fin 6 => x r = true)).card ≤ 2 := by
          have hsub : Finset.univ.filter (fun r : Fin 6 => x r = true) ⊆ {p, q} := by
            intro r hr
            simp [x] at hr ⊢
            exact hr
          have hc := Finset.card_le_card hsub
          have hpaircard : ({p, q} : Finset (Fin 6)).card ≤ 2 := by
            by_cases hpq : p = q <;> simp [hpq]
          omega
        have hxfalse : ∀ r ∈ S i, x r = false := by
          intro r hr
          simp [x]
          constructor <;> intro hpr
          · subst r
            exact hpS hr
          · subst r
            exact hqS hr
        have houtfalse := (hcond i).2 x hcardx hxfalse
        have : (C.wires (List.ofFn x)).getD (o i) false = true := by simpa [hokt] using hval
        rw [this] at houtfalse
        contradiction
      rcases hAeq with hAeq | hBeq
      · have ha_lt : a < 6 + kt := by
          by_contra ha
          have hc : (A).card = 0 := by simp [A, ha]
          rw [hAeq, S_card i] at hc
          omega
        have ha_ge : 6 ≤ a := by
          by_contra ha
          have halt : a < 6 := by omega
          have hc : (Ls C a).card = 1 := by rw [Ls_input C a halt]; simp
          have hAone : A = {⟨a, halt⟩} := by simp [A, ha_lt, Ls_input C a halt]
          have hcA : (A).card = 1 := by simp [hAone]
          rw [hAeq, S_card i] at hcA
          omega
        let k₂ := a - 6
        have haeq : a = 6 + k₂ := by omega
        have hAeqLs : Ls C a = S i := by simpa [A, ha_lt] using hAeq
        refine ⟨kt, k₂, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hLg]
        · rw [hLg, S_card i]
          omega
        · rw [← haeq]
          exact hAeqLs.le
        · rw [← haeq, hAeqLs, S_card i]
          omega
      · have hb_lt : b < 6 + kt := by
          by_contra hb
          have hc : (B).card = 0 := by simp [B, hb]
          rw [hBeq, S_card i] at hc
          omega
        have hb_ge : 6 ≤ b := by
          by_contra hb
          have hblt : b < 6 := by omega
          have hc : (Ls C b).card = 1 := by rw [Ls_input C b hblt]; simp
          have hBone : B = {⟨b, hblt⟩} := by simp [B, hb_lt, Ls_input C b hblt]
          have hcB : (B).card = 1 := by simp [hBone]
          rw [hBeq, S_card i] at hcB
          omega
        let k₂ := b - 6
        have hbeq : b = 6 + k₂ := by omega
        have hBeqLs : Ls C b = S i := by simpa [B, hb_lt] using hBeq
        refine ⟨kt, k₂, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hLg]
        · rw [hLg, S_card i]
          omega
        · rw [← hbeq]
          exact hBeqLs.le
        · rw [← hbeq, hBeqLs, S_card i]
          omega
  let Ti : Fin 3 → Finset ℕ := fun i =>
    (Finset.range n).filter (fun k => Ls C (6 + k) ⊆ S i ∧ 2 ≤ (Ls C (6 + k)).card)
  have hTi (i : Fin 3) : 2 ≤ (Ti i).card := by
    rcases two_gates i with ⟨k₁, k₂, hk₁, hk₂, hk12, hsub₁, hc₁, hsub₂, hc₂⟩
    have hmem₁ : k₁ ∈ Ti i := by simp [Ti, hk₁, hsub₁, hc₁]
    have hmem₂ : k₂ ∈ Ti i := by simp [Ti, hk₂, hsub₂, hc₂]
    have hsub : ({k₁, k₂} : Finset ℕ) ⊆ Ti i := by
      intro k hk
      simp at hk
      rcases hk with rfl | rfl
      · exact hmem₁
      · exact hmem₂
    have hc := Finset.card_le_card hsub
    have hpair : ({k₁, k₂} : Finset ℕ).card = 2 := by simp [hk12]
    omega
  have hdis (i j : Fin 3) (hij : i ≠ j) : Disjoint (Ti i) (Ti j) := by
    rw [Finset.disjoint_left]
    intro k hki hkj
    simp [Ti] at hki hkj
    have hsub : Ls C (6 + k) ⊆ S i ∩ S j := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨hki.2.1 hp, hkj.2.1 hp⟩
    have hc := Finset.card_le_card hsub
    rw [S_inter_card i j hij] at hc
    omega
  have hd01 : Disjoint (Ti 0) (Ti 1) := hdis 0 1 (by decide)
  have hd12 : Disjoint (Ti 1) (Ti 2) := hdis 1 2 (by decide)
  have hd02 : Disjoint (Ti 0) (Ti 2) := hdis 0 2 (by decide)
  have hcard01 : (Ti 0 ∪ Ti 1).card = (Ti 0).card + (Ti 1).card :=
    Finset.card_union_of_disjoint hd01
  have hcard012 : ((Ti 0 ∪ Ti 1) ∪ Ti 2).card = (Ti 0 ∪ Ti 1).card + (Ti 2).card :=
    Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro k hk hk2
      rcases Finset.mem_union.mp hk with hk0 | hk1
      · exact (Finset.disjoint_left.mp hd02) hk0 hk2
      · exact (Finset.disjoint_left.mp hd12) hk1 hk2)
  have hTi_sub (i : Fin 3) : Ti i ⊆ Finset.range n := by
    intro k hk
    simp [Ti] at hk
    simpa using hk.1
  have hsubU : ((Ti 0 ∪ Ti 1) ∪ Ti 2) ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk01 | hk2
    · rcases Finset.mem_union.mp hk01 with hk0 | hk1
      · exact hTi_sub 0 hk0
      · exact hTi_sub 1 hk1
    · exact hTi_sub 2 hk2
  have hcardU_le : ((Ti 0 ∪ Ti 1) ∪ Ti 2).card ≤ n := by
    have := Finset.card_le_card hsubU
    simpa using this
  have hcardU_ge : 6 ≤ ((Ti 0 ∪ Ti 1) ∪ Ti 2).card := by
    rw [hcard012, hcard01]
    have h0 := hTi 0
    have h1 := hTi 1
    have h2 := hTi 2
    omega
  omega
