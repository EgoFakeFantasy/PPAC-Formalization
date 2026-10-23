import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentSyntax

/-! 每个合法内部首槽输入实际取得原数值环境码对；实际表与原码皆由对象存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopCodedEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_at_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g)) :
    Derives Γ (existsInstantiate w a b A t) := by
  have hm := SyntaxTopEnvironmentTyping.instantiate_maps w a b A t f g hi
  let E := SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxMixedImageCodePairs.exists_codes hZ w f g A b a b hw hm)
  have hi2 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.instantiateEnv_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hc := intro_instantiate w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc g.castSucc.castSucc (.conjI hi2 hE)
  have ho := intro_instantiate_pair w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc
  exact of_eq (by simp only [Formula.raise, existsInstantiate_rename]) ho

theorem instantiate_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)) :
    Derives Γ (existsInstantiate w a b A t) := by
  let E := SyntaxTopEnvironmentSyntax.instantiateEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxTopInstantiateExistence.exists_pair hZ w a b A t hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := instantiate_at_tables hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hE
  exact of_eq (by simp only [Formula.raise, existsInstantiate_rename]) ho

theorem abstract_at_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g)) :
    Derives Γ (existsAbstract w a b A B) := by
  have hm := SyntaxTopEnvironmentTyping.abstract_maps w a b A B f g hi
  let E := SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxMixedImageCodePairs.exists_codes hZ w f g a B A b hw hm)
  have hi2 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.abstractEnv_rename]) (SyntaxRenameBinders.under_2 hi E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hc := intro_abstract w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc g.castSucc.castSucc (.conjI hi2 hE)
  have ho := intro_abstract_pair w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc
  exact of_eq (by simp only [Formula.raise, existsAbstract_rename]) ho

theorem abstract_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) :
    Derives Γ (existsAbstract w a b A B) := by
  let E := SyntaxTopEnvironmentSyntax.abstractEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxTopAbstractExistence.exists_pair hZ w a b A B hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := abstract_at_tables hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hE
  exact of_eq (by simp only [Formula.raise, existsAbstract_rename]) ho

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentExistence
