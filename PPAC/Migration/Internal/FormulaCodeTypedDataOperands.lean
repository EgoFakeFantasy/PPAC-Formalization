import PPAC.Migration.Internal.FormulaCodeRootSlots

/-! 零至三个真实字段见证的对象存在消去，恢复同根FormulaCode；不预设Constructor。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataOperands
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax SyntaxSlotSyntax SyntaxFieldsFromSlots
open FormulaCodeSyntax FormulaCodeTypedDataSyntax FormulaCodeAllowedAritySyntax FormulaCodeRootSlots
open StructuralTreeOperatorSyntax (shape shape_rename)
open SyntaxCheckedSlotExists (existsSlot)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem arity0 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (hk : 0 = expectedArity tag) (w n b f t p l g : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (shape w n t p l g)) (hnt : Derives Γ (numeral tag t))
    (hnl : Derives Γ (numeral 0 l)) (hcheck : Derives Γ (rootCheck tag w g b f)) :
    Derives Γ (formulaCode w n b f) := by
  exact code_at_arity hZ 0 tag ht hk w n b f t p l g Fin.elim0 hw hs hnt hnl (.eqRefl g) hcheck

theorem arity1 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (hk : 1 = expectedArity tag) (w n b f t p l g : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (shape w n t p l g)) (hnt : Derives Γ (numeral tag t))
    (hnl : Derives Γ (numeral 1 l)) (hcheck : Derives Γ (rootCheck tag w g b f)) :
    Derives Γ (formulaCode w n b f) := by
  have he0 := at_arity 1 tag ht hk w g b f (⟨0, by decide⟩ : Fin 1) hcheck
  let S0 := slot g.castSucc 0 (Fin.last m)
  let Δ0 := Context.add S0 (Context.image Formula.raise Γ)
  change Derives Γ (.ex S0) at he0
  apply Derives.exE he0
  have hc0 : Derives Δ0 (rootCheck tag w.castSucc g.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hcheck S0
  have lift {P : Formula m} (hp : Derives Γ P) : Derives Δ0 P.raise := under (hp) S0
  have hZ1 := ZFContext.under (hZ) S0
  have hw1 : Derives Δ0 (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using lift hw
  have hs1 : Derives Δ0 (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using lift hs
  have hnt1 : Derives Δ0 (numeral tag t.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnt
  have hnl1 : Derives Δ0 (numeral 1 l.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnl
  have hslt0 : Derives Δ0 S0 := .hyp (Or.inl rfl)
  have hv0 : Derives Δ0 (slot g.castSucc 0 (Fin.last m)) := by
    simpa only [S0, Formula.raise, slot_rename] using hslt0
  have hslots : Derives Δ0 (slots 1 g.castSucc (fun _ : Fin 1 => (Fin.last m))) := by
    apply intro_slots
    intro j
    have hj : j = (0 : Fin 1) := by omega
    subst j
    exact hv0
  have hout := code_at_arity hZ1 1 tag ht hk w.castSucc n.castSucc b.castSucc f.castSucc t.castSucc p.castSucc l.castSucc g.castSucc (fun _ : Fin 1 => (Fin.last m)) hw1 hs1 hnt1 hnl1 hslots hc0
  simpa only [Formula.raise, formulaCode_rename] using hout

theorem arity2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (hk : 2 = expectedArity tag) (w n b f t p l g : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (shape w n t p l g)) (hnt : Derives Γ (numeral tag t))
    (hnl : Derives Γ (numeral 2 l)) (hcheck : Derives Γ (rootCheck tag w g b f)) :
    Derives Γ (formulaCode w n b f) := by
  have he0 := at_arity 2 tag ht hk w g b f (⟨0, by decide⟩ : Fin 2) hcheck
  let S0 := slot g.castSucc 0 (Fin.last m)
  let Δ0 := Context.add S0 (Context.image Formula.raise Γ)
  change Derives Γ (.ex S0) at he0
  apply Derives.exE he0
  have hc0 : Derives Δ0 (rootCheck tag w.castSucc g.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hcheck S0
  have he1 := at_arity 2 tag ht hk w.castSucc g.castSucc b.castSucc f.castSucc (⟨1, by decide⟩ : Fin 2) hc0
  let S1 := slot g.castSucc.castSucc 1 (Fin.last (m+1))
  let Δ1 := Context.add S1 (Context.image Formula.raise Δ0)
  change Derives Δ0 (.ex S1) at he1
  apply Derives.exE he1
  have hc1 : Derives Δ1 (rootCheck tag w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hc0 S1
  have lift {P : Formula m} (hp : Derives Γ P) : Derives Δ1 P.raise.raise := under (under (hp) S0) S1
  have hZ2 := ZFContext.under (ZFContext.under (hZ) S0) S1
  have hw2 : Derives Δ1 (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ1 (shape w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using lift hs
  have hnt2 : Derives Δ1 (numeral tag t.castSucc.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnt
  have hnl2 : Derives Δ1 (numeral 2 l.castSucc.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnl
  have hslt0 : Derives Δ0 S0 := .hyp (Or.inl rfl)
  have hv0 : Derives Δ1 (slot g.castSucc.castSucc 0 (Fin.last m).castSucc) := by
    simpa only [S0, Formula.raise, slot_rename] using under (hslt0) S1
  have hslt1 : Derives Δ1 S1 := .hyp (Or.inl rfl)
  have hv1 : Derives Δ1 (slot g.castSucc.castSucc 1 (Fin.last (m+1))) := by
    simpa only [S1, Formula.raise, slot_rename] using hslt1
  have hslots : Derives Δ1 (slots 2 g.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc (Fin.last (m+1)))) := by
    apply intro_slots
    intro j
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact hv0
    · exact hv1
  have hout := code_at_arity hZ2 2 tag ht hk w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc (Fin.last (m+1))) hw2 hs2 hnt2 hnl2 hslots hc1
  simpa only [Formula.raise, formulaCode_rename] using hout

theorem arity3 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (hk : 3 = expectedArity tag) (w n b f t p l g : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (shape w n t p l g)) (hnt : Derives Γ (numeral tag t))
    (hnl : Derives Γ (numeral 3 l)) (hcheck : Derives Γ (rootCheck tag w g b f)) :
    Derives Γ (formulaCode w n b f) := by
  have he0 := at_arity 3 tag ht hk w g b f (⟨0, by decide⟩ : Fin 3) hcheck
  let S0 := slot g.castSucc 0 (Fin.last m)
  let Δ0 := Context.add S0 (Context.image Formula.raise Γ)
  change Derives Γ (.ex S0) at he0
  apply Derives.exE he0
  have hc0 : Derives Δ0 (rootCheck tag w.castSucc g.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hcheck S0
  have he1 := at_arity 3 tag ht hk w.castSucc g.castSucc b.castSucc f.castSucc (⟨1, by decide⟩ : Fin 3) hc0
  let S1 := slot g.castSucc.castSucc 1 (Fin.last (m+1))
  let Δ1 := Context.add S1 (Context.image Formula.raise Δ0)
  change Derives Δ0 (.ex S1) at he1
  apply Derives.exE he1
  have hc1 : Derives Δ1 (rootCheck tag w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hc0 S1
  have he2 := at_arity 3 tag ht hk w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (⟨2, by decide⟩ : Fin 3) hc1
  let S2 := slot g.castSucc.castSucc.castSucc 2 (Fin.last (m+2))
  let Δ2 := Context.add S2 (Context.image Formula.raise Δ1)
  change Derives Δ1 (.ex S2) at he2
  apply Derives.exE he2
  have hc2 : Derives Δ2 (rootCheck tag w.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, rootCheck_rename] using under hc1 S2
  have lift {P : Formula m} (hp : Derives Γ P) : Derives Δ2 P.raise.raise.raise := under (under (under (hp) S0) S1) S2
  have hZ3 := ZFContext.under (ZFContext.under (ZFContext.under (hZ) S0) S1) S2
  have hw3 : Derives Δ2 (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using lift hw
  have hs3 : Derives Δ2 (shape w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using lift hs
  have hnt3 : Derives Δ2 (numeral tag t.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnt
  have hnl3 : Derives Δ2 (numeral 3 l.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, numeral_rename] using lift hnl
  have hslt0 : Derives Δ0 S0 := .hyp (Or.inl rfl)
  have hv0 : Derives Δ2 (slot g.castSucc.castSucc.castSucc 0 (Fin.last m).castSucc.castSucc) := by
    simpa only [S0, Formula.raise, slot_rename] using under (under (hslt0) S1) S2
  have hslt1 : Derives Δ1 S1 := .hyp (Or.inl rfl)
  have hv1 : Derives Δ2 (slot g.castSucc.castSucc.castSucc 1 (Fin.last (m+1)).castSucc) := by
    simpa only [S1, Formula.raise, slot_rename] using under (hslt1) S2
  have hslt2 : Derives Δ2 S2 := .hyp (Or.inl rfl)
  have hv2 : Derives Δ2 (slot g.castSucc.castSucc.castSucc 2 (Fin.last (m+2))) := by
    simpa only [S2, Formula.raise, slot_rename] using hslt2
  have hslots : Derives Δ2 (slots 3 g.castSucc.castSucc.castSucc (SyntaxAtomSyntax.three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))) := by
    apply intro_slots
    intro j
    have hj : j = (0 : Fin 3) ∨ j = (1 : Fin 3) ∨ j = (2 : Fin 3) := by omega
    rcases hj with rfl | rfl | rfl
    · exact hv0
    · exact hv1
    · exact hv2
  have hout := code_at_arity hZ3 3 tag ht hk w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (SyntaxAtomSyntax.three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) hw3 hs3 hnt3 hnl3 hslots hc2
  simpa only [Formula.raise, formulaCode_rename] using hout
end PPAC.Migration.Internal.FormulaCodeTypedDataOperands
