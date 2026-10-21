import PPAC.Migration.Internal.FormulaCodeTypedDataForward

/-! 实际有限槽位恢复全内部图边定律；不从Prop抽取宿主字段数组。 -/
namespace PPAC.Migration.Internal.SyntaxFieldsFromSlots
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNumeralSyntax SyntaxSlotSyntax SyntaxPositionSyntax SyntaxForestSyntax
open StructuralListFieldGraphSyntax (fields fields_rename)
open SyntaxForestFields (graphLaw graphLaw_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def slots {m} : (k : Nat) → Fin m → (Fin k → Fin m) → Formula m
  | 0, g, _ => .equal g g
  | k+1, g, xs => (slots k g (fun j => xs j.castSucc)).conj (slot g k (xs (Fin.last k)))

theorem slots_rename {m n} (k : Nat) (g : Fin m) (xs : Fin k → Fin m) (r : Fin m → Fin n) :
    (slots k g xs).rename r = slots k (r g) (fun j => r (xs j)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [slots, Formula.rename, slot_rename, ih]

theorem slots_at {m} {Γ : Context m} (k : Nat) (g : Fin m) (xs : Fin k → Fin m) (j : Fin k)
    (hh : Derives Γ (slots k g xs)) : Derives Γ (slot g j.val (xs j)) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    revert hh
    refine Fin.lastCases ?_ (fun i => ?_) j
    · intro hh; exact .conjR hh
    · intro hh; exact ih (fun a => xs a.castSucc) i (.conjL hh)

theorem intro_slots {m} {Γ : Context m} (k : Nat) (g : Fin m) (xs : Fin k → Fin m)
    (hh : ∀ j, Derives Γ (slot g j.val (xs j))) : Derives Γ (slots k g xs) := by
  induction k with
  | zero => exact .eqRefl g
  | succ k ih => exact .conjI (ih (fun j => xs j.castSucc) (fun j => hh j.castSucc)) (hh (Fin.last k))

theorem slot_at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (g y i : Fin m) (j : Nat)
    (hs : Derives Γ (slot g j y)) (hi : Derives Γ (numeral j i)) : Derives Γ (edge g i y) := by
  let B := body g j y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_slot g j y _ hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi1 : Derives Δ (numeral j i.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using under hi B
  have he := SyntaxNumerals.unique (ZFContext.under hZ B) j (Fin.last m) i.castSucc (.conjL hB) hi1
  simpa only [Formula.raise, edge_rename] using
    IterationValues.edge_subst_input g.castSucc (Fin.last m) i.castSucc y.castSucc he (.conjR hB)

theorem slot_natural {m} {Γ : Context m} (g w y : Fin m) (j : Nat)
    (hs : Derives Γ (slot g j y)) (hb : Derives Γ (SequenceSyntax.bounded g w)) : Derives Γ (.mem y w) := by
  let B := body g j y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_slot g j y _ hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hb1 : Derives Δ (SequenceSyntax.bounded g.castSucc w.castSucc) := by
    simpa only [Formula.raise, SequenceSyntax.bounded_rename] using under hb B
  exact .impE (SequenceSyntax.bounded_at _ _ _ _ hb1) (.conjR hB)

theorem inputs_of_slots {m} {Γ : Context m} (k : Nat) (w p l g : Fin m) (xs : Fin k → Fin m)
    (hf : Derives Γ (fields w p l g)) (hs : Derives Γ (slots k g xs)) : Derives Γ (inputs k w xs) := by
  apply intro_inputs k w xs
  intro j
  exact slot_natural g w (xs j) j.val (slots_at k g xs j hs) (.conjR (.conjL hf))

theorem full_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w p l g : Fin m)
    (xs : Fin k → Fin m) (i y : Fin m) (hf : Derives Γ (fields w p l g))
    (hl : Derives Γ (numeral k l)) (hs : Derives Γ (slots k g xs)) :
    Derives Γ ((edge g i y).iff (positions k xs i y)) := by
  have hm := SyntaxNumeralMembers.member_iff hZ k l i hl
  have hfun : Derives Γ (functionOn g l) := .conjL (.conjL hf)
  apply Derives.conjI
  · apply Derives.impI
    let E := edge g i y
    let Δ := Context.add E Γ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hd := GraphProperties.domain_of_edge g l i y (ZFContext.arithmetic (ZFContext.add hZ E)).base.extensionality (add hfun E) hE
    have hb := Derives.impE (add (.conjL hm) E) hd
    have hh : Derives Δ ((below k i).imp (positions k xs i y)) := by
      apply below_imp k i (positions k xs i y)
      intro j
      apply Derives.impI
      let J := numeral j.val i
      have hJ : Derives (Context.add J Δ) J := .hyp (Or.inl rfl)
      have hx := slot_at_index (ZFContext.add (ZFContext.add hZ E) J) g (xs j) i j.val
        (add (add (slots_at k g xs j hs) E) J) hJ
      have he := GraphProperties.single_valued g l i y (xs j)
        (ZFContext.arithmetic (ZFContext.add (ZFContext.add hZ E) J)).base.extensionality
        (add (add hfun E) J) (add hE J) hx
      exact intro_position k xs j i y hJ he
    exact .impE hh hb
  · apply positions_imp k xs i y (edge g i y)
    intro j
    apply Derives.impI
    let P := (numeral j.val i).conj (.equal y (xs j))
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have hx := slot_at_index (ZFContext.add hZ P) g (xs j) i j.val (add (slots_at k g xs j hs) P) (.conjL hP)
    exact GraphPointwiseSyntax.edge_subst_output g i (xs j) y (eq_symm (.conjR hP)) hx

theorem all_edges {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w p l g : Fin m)
    (xs : Fin k → Fin m) (hf : Derives Γ (fields w p l g))
    (hl : Derives Γ (numeral k l)) (hs : Derives Γ (slots k g xs)) : Derives Γ (graphLaw k xs g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hf2 : Derives Δ (fields w.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, fields_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hl2 : Derives Δ (numeral k l.castSucc.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hl)
  have hs2 : Derives Δ (slots k g.castSucc.castSucc (fun j => (xs j).castSucc.castSucc)) := by
    simpa only [Formula.raise, slots_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  exact full_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc)
    k _ _ _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) hf2 hl2 hs2
end PPAC.Migration.Internal.SyntaxFieldsFromSlots
