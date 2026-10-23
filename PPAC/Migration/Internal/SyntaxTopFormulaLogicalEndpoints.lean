import PPAC.Migration.Internal.SyntaxTopFormulaSharedEndpoints

/-! 首槽公式空原子、否定、四二元联结词的精确递归端点；子判断同样不含外部环境见证。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaLogicalEndpoints
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
open FormulaCodeCongruence (conj_congr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_nullary_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w a b A t n q  R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hi : Derives Γ (instantiateInput w a b A t n)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((instantiated w a b A t n q).iff (.equal q n)) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S A b a b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S he)
  have hP := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t n q R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxMixedFormulaEndpoints.nullary_iff hZ truth w R S A b a b n q hw hm hc)

theorem instantiate_nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w a b A t n q  : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) : Derives Γ ((instantiated w a b A t n q).iff (.equal q n)) := by
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w.castSucc.castSucc Fin.elim0 n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (SyntaxRenameBinders.under_2 hc C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := instantiate_nullary_at_codes hZ2 truth w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, instantiated_rename]) ho

theorem instantiate_negation_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q x X R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hi : Derives Γ (instantiateInput w a b A t n)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w X q)) :
    Derives Γ ((instantiated w a b A t n q).iff (instantiated w a b A t x X)) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S A b a b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S he)
  have hP := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t n q R S hw he
  have hM := SyntaxMixedFormulaEndpoints.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S A b a b n q x X hw hm hc hd
  have hX := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t x X R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxTypeLocalTransfer.iff_trans hM (.conjI (.conjR hX) (.conjL hX)))

theorem instantiate_negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w X q)) : Derives Γ ((instantiated w a b A t n q).iff (instantiated w a b A t x X)) := by
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := instantiate_negation_at_codes hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, instantiated_rename]) ho

theorem instantiate_binary_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a b A t n q x y X Y R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hi : Derives Γ (instantiateInput w a b A t n)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((instantiated w a b A t n q).iff ((instantiated w a b A t x X).conj (instantiated w a b A t y Y))) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S A b a b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S he)
  have hP := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t n q R S hw he
  have hM := SyntaxMixedFormulaEndpoints.binary_iff hZ kind w R S A b a b n q x y X Y hw hm hc hd
  have hX := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t x X R S hw he
  have hY := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t y Y R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxTypeLocalTransfer.iff_trans hM
    (conj_congr (.conjI (.conjR hX) (.conjL hX)) (.conjI (.conjR hY) (.conjL hY))))

theorem instantiate_binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a b A t n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) : Derives Γ ((instantiated w a b A t n q).iff ((instantiated w a b A t x X).conj (instantiated w a b A t y Y))) := by
  let C := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := instantiate_binary_at_codes hZ2 kind w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, instantiated_rename]) ho

theorem abstract_nullary_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w a b A B n q  R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (abstractInput w a b A B n)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((abstracted w a b A B n q).iff (.equal q n)) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a B A b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he)
  have hP := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxMixedFormulaEndpoints.nullary_iff hZ truth w R S a B A b n q hw hm hc)

theorem abstract_nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w a b A B n q  : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) : Derives Γ ((abstracted w a b A B n q).iff (.equal q n)) := by
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w.castSucc.castSucc Fin.elim0 n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (SyntaxRenameBinders.under_2 hc C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := abstract_nullary_at_codes hZ2 truth w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, abstracted_rename]) ho

theorem abstract_negation_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q x X R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (abstractInput w a b A B n)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w X q)) :
    Derives Γ ((abstracted w a b A B n q).iff (abstracted w a b A B x X)) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a B A b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he)
  have hP := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S hw he
  have hM := SyntaxMixedFormulaEndpoints.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S a B A b n q x X hw hm hc hd
  have hX := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B x X R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxTypeLocalTransfer.iff_trans hM (.conjI (.conjR hX) (.conjL hX)))

theorem abstract_negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w X q)) : Derives Γ ((abstracted w a b A B n q).iff (abstracted w a b A B x X)) := by
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := abstract_negation_at_codes hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, abstracted_rename]) ho

theorem abstract_binary_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a b A B n q x y X Y R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (abstractInput w a b A B n)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((abstracted w a b A B n q).iff ((abstracted w a b A B x X).conj (abstracted w a b A B y Y))) := by
  have hm : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a B A b n) :=
    .conjI (.conjR hi) (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he)
  have hP := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S hw he
  have hM := SyntaxMixedFormulaEndpoints.binary_iff hZ kind w R S a B A b n q x y X Y hw hm hc hd
  have hX := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B x X R S hw he
  have hY := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B y Y R S hw he
  exact SyntaxTypeLocalTransfer.iff_trans hP (SyntaxTypeLocalTransfer.iff_trans hM
    (conj_congr (.conjI (.conjR hX) (.conjL hX)) (.conjI (.conjR hY) (.conjL hY))))

theorem abstract_binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a b A B n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) : Derives Γ ((abstracted w a b A B n q).iff ((abstracted w a b A B x X).conj (abstracted w a b A B y Y))) := by
  let C := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi C)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (SyntaxRenameBinders.under_2 hc C)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (SyntaxRenameBinders.under_2 hd C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ho := abstract_binary_at_codes hZ2 kind w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hC hi2 hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, abstracted_rename]) ho

end PPAC.Migration.Internal.SyntaxTopFormulaLogicalEndpoints
