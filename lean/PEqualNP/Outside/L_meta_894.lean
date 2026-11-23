import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_894

private def base : Finset (Fin 73) := {0, 1, 3, 7, 15, 31, 36, 54, 63}

private def line (shift : Fin 73) : Finset (Fin 73) :=
  base.image (fun p => p + shift)

private def distinctPairs : Finset (Fin 73 × Fin 73) :=
  (base ×ˢ base).filter (fun ab => ab.1 ≠ ab.2)

private def difference (ab : Fin 73 × Fin 73) : Fin 73 := ab.2 - ab.1

-- The 72 ordered pairs of distinct base points give the 72 nonzero differences.
set_option maxRecDepth 10000 in
private lemma differences :
    distinctPairs.image difference = (Finset.univ : Finset (Fin 73)).erase 0 := by
  decide

private lemma pair_mem {a b : Fin 73} :
    (a, b) ∈ distinctPairs ↔ a ∈ base ∧ b ∈ base ∧ a ≠ b := by
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product]
  exact and_assoc

set_option maxRecDepth 10000 in
private lemma difference_injective : Set.InjOn difference ↑distinctPairs := by
  apply Finset.card_image_iff.mp
  rw [differences]
  decide

private lemma line_card (i : Fin 73) : (line i).card = 8 + 1 := by
  rw [line, Finset.card_image_of_injective _ (add_left_injective i)]
  decide

private lemma line_intersection (i j : Fin 73) (hij : i ≠ j) :
    (line i ∩ line j).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  apply Classical.byContradiction
  intro hpq
  obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
  obtain ⟨hqi, hqj⟩ := Finset.mem_inter.mp hq
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hpi
  obtain ⟨b, hb, hqb⟩ := Finset.mem_image.mp hqi
  obtain ⟨c, hc, hpc⟩ := Finset.mem_image.mp hpj
  obtain ⟨d, hd, hqd⟩ := Finset.mem_image.mp hqj
  have hdiff : difference (a, b) = difference (c, d) := by
    change b - a = d - c
    calc
      b - a = (b + i) - (a + i) := by abel
      _ = (d + j) - (c + j) := by rw [hqb, hpa, hqd, hpc]
      _ = d - c := by abel
  have hab : a ≠ b := by
    intro h
    apply hpq
    rw [← hpa, ← hqb, h]
  have hcd : c ≠ d := by
    intro h
    apply hpq
    rw [← hpc, ← hqd, h]
  have hac : a = c :=
    congrArg Prod.fst (difference_injective (pair_mem.mpr ⟨ha, hb, hab⟩)
      (pair_mem.mpr ⟨hc, hd, hcd⟩) hdiff)
  apply hij
  apply add_left_cancel (a := c)
  simpa [hac] using hpa.trans hpc.symm

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_prefix (gates : List Gate) (w : List Bool) :
    ∃ tail : List Bool, gates.foldl step w = w ++ tail ∧ tail.length = gates.length := by
  induction gates generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gates ih =>
    obtain ⟨tail, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tail, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

private lemma fold_length (gates : List Gate) (w : List Bool) :
    (gates.foldl step w).length = w.length + gates.length := by
  obtain ⟨tail, ht, hl⟩ := fold_prefix gates w
  simp [ht, hl]

private lemma prefix_eval (gates : List Gate) (w : List Bool) (k i : ℕ)
    (hi : i < w.length + (gates.take k).length) :
    (gates.foldl step w).getD i false = ((gates.take k).foldl step w).getD i false := by
  obtain ⟨tail, ht, _⟩ := fold_prefix (gates.drop k) ((gates.take k).foldl step w)
  have hs : gates.foldl step w =
      (gates.drop k).foldl step ((gates.take k).foldl step w) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [hs, ht, List.getD_append]
  simpa only [fold_length] using hi

private lemma getD_append_singleton_of_ne (w : List Bool) (b : Bool) (i : ℕ)
    (hi : i ≠ w.length) : (w ++ [b]).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · have hw : w.length ≤ i := by omega
    have hw' : (w ++ [b]).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hw', List.getD_eq_default _ _ hw]

-- Tracing one gate backwards replaces its output by at most two inputs.
private lemma support_bound (gates : List Gate) (fan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (n : ℕ) (outputs : Finset ℕ) :
    ∃ support : Finset ℕ, support.card ≤ outputs.card + gates.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ support, x.getD i false = y.getD i false) →
        ∀ i ∈ outputs, (gates.foldl step x).getD i false = (gates.foldl step y).getD i false := by
  induction gates using List.reverseRecOn generalizing outputs with
  | nil => exact ⟨outputs, by simp, by simp⟩
  | append_singleton gates g ih =>
    have hfan : ∀ a ∈ gates, a.inputs.length ≤ 2 :=
      fun a ha => fan a (List.mem_append_left _ ha)
    let index := n + gates.length
    let needed := if index ∈ outputs then outputs.erase index ∪ g.inputs.toFinset else outputs
    have hcard : needed.card ≤ outputs.card + 1 := by
      by_cases h : index ∈ outputs
      · simp only [needed, ite_eq_left h]
        have hu := Finset.card_union_le (outputs.erase index) g.inputs.toFinset
        have he := Finset.card_erase_add_one h
        have hin := (List.toFinset_card_le g.inputs).trans (fan g (by simp))
        omega
      · simp [needed, h]
    obtain ⟨support, hsupport, hagree⟩ := ih hfan needed
    refine ⟨support, by simp; omega, ?_⟩
    intro x y hx hy hxy i hi
    have hprev := hagree x y hx hy hxy
    have hlenx : (gates.foldl step x).length = index := by simp [index, fold_length, hx]
    have hleny : (gates.foldl step y).length = index := by simp [index, fold_length, hy]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
    by_cases heq : i = index
    · subst i
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [hlenx, hleny, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact hprev j (by
        simp only [needed, ite_eq_left hi, Finset.mem_union, List.mem_toFinset]
        exact Or.inr hj)
    · rw [getD_append_singleton_of_ne _ _ _ (by omega),
        getD_append_singleton_of_ne _ _ _ (by omega)]
      apply hprev
      by_cases hn : index ∈ outputs
      · simp only [needed, ite_eq_left hn]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hi⟩)
      · simpa [needed, hn] using hi

private def single (p : Fin 73) (q : Fin 73) : Bool := decide (q = p)

private lemma single_line (i p : Fin 73) :
    decide (∃ v ∈ line i, single p v = true) = true ↔ p ∈ line i := by
  simp [single]

private lemma false_line (i : Fin 73) :
    decide (∃ v ∈ line i, (false : Bool) = true) = false := by simp

private lemma getD_single_eq_false_of_ne (p : Fin 73) (j : ℕ) (h : j ≠ p.val) :
    (List.ofFn (single p)).getD j false = (List.ofFn (fun _ : Fin 73 => false)).getD j false := by
  by_cases hj : j < 73
  · have hne : (⟨j, hj⟩ : Fin 73) ≠ p := fun he => h (congrArg Fin.val he)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some,
      single, decide_eq_false hne]
  · rw [List.getD_eq_default, List.getD_eq_default] <;> simp <;> omega

set_option maxHeartbeats 1200000 in
private lemma fanin_bound (gates : List Gate) (out : Fin 73 → ℕ)
    (fan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (heval : ∀ (i : Fin 73) (x : Fin 73 → Bool),
      (⟨gates, out i⟩ : Circuit).eval (List.ofFn x) =
        decide (∃ p ∈ line i, x p = true)) : 80 ≤ gates.length := by
  have hupper (i : Fin 73) : out i < 73 + gates.length := by
    obtain ⟨p, hp⟩ : (line i).Nonempty := Finset.card_pos.mp (by rw [line_card]; decide)
    have ht := (single_line i p).mpr hp
    rw [← heval i (single p)] at ht
    change (gates.foldl step (List.ofFn (single p))).getD (out i) false = true at ht
    by_contra hn
    have hlen : (gates.foldl step (List.ofFn (single p))).length ≤ out i := by
      simpa only [fold_length, List.length_ofFn] using Nat.le_of_not_gt hn
    rw [List.getD_eq_default _ _ hlen] at ht
    exact Bool.noConfusion ht
  have hlower (i : Fin 73) : 80 ≤ out i := by
    let k := out i + 1 - 73
    have hkle : k ≤ gates.length := by dsimp [k]; have := hupper i; omega
    have hlen : (gates.take k).length = k := by simp [List.length_take, min_eq_left hkle]
    have hi : out i < 73 + (gates.take k).length := by rw [hlen]; dsimp [k]; omega
    have hfan : ∀ g ∈ gates.take k, g.inputs.length ≤ 2 :=
      fun g hg => fan g (List.mem_of_mem_take hg)
    obtain ⟨support, hcard, hsupport⟩ := support_bound (gates.take k) hfan 73 {out i}
    have hsub : (line i).image Fin.val ⊆ support := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      by_contra hn
      have hdepends := hsupport (List.ofFn (single p)) (List.ofFn (fun _ : Fin 73 => false))
        (List.length_ofFn) (List.length_ofFn)
        (fun a ha => getD_single_eq_false_of_ne p a (fun e => hn (e ▸ ha))) (out i) (by simp)
      rw [← prefix_eval gates (List.ofFn (single p)) k (out i)
          (by simpa only [List.length_ofFn] using hi),
        ← prefix_eval gates (List.ofFn (fun _ : Fin 73 => false)) k (out i)
          (by simpa only [List.length_ofFn] using hi)] at hdepends
      change (⟨gates, out i⟩ : Circuit).eval (List.ofFn (single p)) =
        (⟨gates, out i⟩ : Circuit).eval (List.ofFn (fun _ : Fin 73 => false)) at hdepends
      rw [heval, heval, (single_line i p).mpr hp, false_line] at hdepends
      exact Bool.noConfusion hdepends
    have hline := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, line_card] at hline
    simp only [Finset.card_singleton, hlen] at hcard
    dsimp [k] at hcard
    omega
  have hout : Function.Injective out := by
    intro i j hij
    by_contra hne
    have hsame : line i = line j := by
      ext p
      rw [← single_line i p, ← single_line j p, ← heval, ← heval, hij]
    have := line_intersection i j hne
    rw [hsame, Finset.inter_self, line_card] at this
    omega
  have hrange : (Finset.univ.image out) ⊆ Finset.Ico 80 (73 + gates.length) := by
    intro o ho
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ho
    exact Finset.mem_Ico.mpr ⟨hlower i, hupper i⟩
  have hcount := Finset.card_le_card hrange
  rw [Finset.card_image_of_injective _ hout, Finset.card_univ, Fintype.card_fin, Nat.card_Ico] at hcount
  omega

end PEqualNP.Outside.L_meta_894

open PEqualNP.Outside.L_meta_894 in
theorem PEqualNP.Outside.L_meta_894 : ((∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length) → ∀ (L5 : List PEqualNP.CircuitLowerBounds.Gate) (out5 : Fin 73 → ℕ), (∀ ga5 ∈ L5, (ga5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ga5.inputs.length ≤ 2) → Set.ncard {ic5 : Fin L5.length | (L5.get ic5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ 3 → (∀ (ja5 : ℕ) (gb5 : PEqualNP.CircuitLowerBounds.Gate), L5[ja5]? = some gb5 → gb5.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun xa5 : Fin 73 → Bool => (gb5.inputs.map (fun ia5 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L5.take ja5, 0⟩ (List.ofFn xa5)).getD ia5 false)).headD false)) → (∀ (wa5 : Fin 73) (xb5 : Fin 73 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L5, out5 wa5⟩ (List.ofFn xb5) = decide (∃ va5 ∈ (({0, 1, 3, 7, 15, 31, 36, 54, 63} : Finset (Fin 73)).image (fun ua5 => ua5 + wa5)), xb5 va5 = true)) → 80 ≤ L5.length := by
  intro _ gates outputs hgate _ _ houtput
  exact fanin_bound gates outputs (fun g hg => (hgate g hg).2) houtput
