import PPAC.Migration.Internal.SyntaxTopFormulaFieldSyntax

/-! 合法原源/目标构造下首槽公式原子端点和实际双表量词端点的精确双条件。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaSharedEndpoints
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax SyntaxTopFormulaFieldSyntax
open FormulaCodeCongruence (ex_congr)
open SyntaxRenameFieldsTransfer (guarded_congr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_equal_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((instantiated w a b A t n q).iff (instantiateEqual w a b A t x y X Y)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  exact SyntaxMixedFormulaEndpoints.equality_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc hw2 hm hc2 hd2

theorem instantiate_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q z Z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((instantiated w a b A t n q).iff (instantiateMember w a b A t z Z x y X Y)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc Z.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  exact SyntaxMixedFormulaEndpoints.membership_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc z.castSucc.castSucc Z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc hw2 hm hc2 hd2

theorem instantiate_advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w a b A t n q x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q)) :
    Derives Γ ((instantiated w a b A t n q).iff (instantiateAdvanced w a b A t x X)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  cases universal
  · exact SyntaxMixedFormulaEndpoints.single_iff hZ2 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc hw2 hm hc2 hd2
  · exact SyntaxMixedFormulaEndpoints.single_iff hZ2 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc hw2 hm hc2 hd2

theorem abstract_equal_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((abstracted w a b A B n q).iff (abstractEqual w a b A B x y X Y)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.abstract_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  exact SyntaxMixedFormulaEndpoints.equality_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc hw2 hm hc2 hd2

theorem abstract_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q z Z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((abstracted w a b A B n q).iff (abstractMember w a b A B z Z x y X Y)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc.castSucc Z.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.abstract_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  exact SyntaxMixedFormulaEndpoints.membership_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc z.castSucc.castSucc Z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc hw2 hm hc2 hd2

theorem abstract_advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w a b A B n q x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q)) :
    Derives Γ ((abstracted w a b A B n q).iff (abstractAdvanced w a b A B x X)) := by
  apply ex_congr
  apply ex_congr
  apply guarded_congr
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjR hi2) (SyntaxTopCodedEnvironmentTyping.abstract_lists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC)
  cases universal
  · exact SyntaxMixedFormulaEndpoints.single_iff hZ2 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc hw2 hm hc2 hd2
  · exact SyntaxMixedFormulaEndpoints.single_iff hZ2 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc hw2 hm hc2 hd2

end PPAC.Migration.Internal.SyntaxTopFormulaSharedEndpoints
