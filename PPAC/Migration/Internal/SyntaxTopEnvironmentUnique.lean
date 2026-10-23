import PPAC.Migration.Internal.SyntaxTopEnvironmentSubst

/-! 两类首槽环境对的实际唯一性；隐藏恒等表和新bound0项码全部按原对象等词规则对齐。 -/
namespace PPAC.Migration.Internal.SyntaxTopEnvironmentUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopEnvironmentSyntax
open SyntaxTopEnvironmentSubst
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g F G u U : Fin m)
    (h1 : Derives Γ (instantiateData w a b A t f g u))
    (h2 : Derives Γ (instantiateData w a b A t F G U)) : Derives Γ ((Formula.equal f F).conj (.equal g G)) := by
  have eu := SyntaxVariableTableUnique.identity_unique hZ true w a b u U (.conjL h1) (.conjL h2)
  have hp := prefix_base w u a a b t A f U eu (.conjL (.conjR h1))
  have ef := SyntaxTermImagePrefixGraph.unique hZ w U a a b t A f F hp (.conjL (.conjR h2))
  have eg := SyntaxVariableTableUnique.identity_unique hZ false w a b g G (.conjR (.conjR h1)) (.conjR (.conjR h2))
  exact .conjI ef eg

theorem abstract_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g F G u z n U Z N : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (abstractData w a b A B f g u z n))
    (h2 : Derives Γ (abstractData w a b A B F G U Z N)) : Derives Γ ((Formula.equal f F).conj (.equal g G)) := by
  have ef := SyntaxVariableTableUnique.shifted_unique hZ true w a A b f F (.conjL h1) (.conjL h2)
  have eu := SyntaxVariableTableUnique.identity_unique hZ false w A b u U (.conjL (.conjR h1)) (.conjL (.conjR h2))
  have en := SyntaxMixedImageBinderAlign.head_unique hZ w A b z n Z N hw (.conjL (.conjR (.conjR h1))) (.conjL (.conjR (.conjR h2)))
  have hp := prefix_base w u b A b n B g U eu (.conjR (.conjR (.conjR h1)))
  have hq := prefix_head w U b A b n B g N (.conjR en) hp
  have eg := SyntaxTermImagePrefixGraph.unique hZ w U b A b N B g G hq (.conjR (.conjR (.conjR h2)))
  exact .conjI ef eg

theorem instantiate_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g F G : Fin m)
     (h1 : Derives Γ (instantiateEnv w a b A t f g)) (h2 : Derives Γ (instantiateEnv w a b A t F G)) :
    Derives Γ ((Formula.equal f F).conj (.equal g G)) := by
  let D := instantiateBody w a b A t f g
  let Ξ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) h1
  have h2k : Derives Ξ (instantiateEnv w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc F.castSucc G.castSucc) := of_eq (by simp only [Formula.raise, instantiateEnv_rename]) (under h2 D)
  let E := instantiateBody w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc F.castSucc G.castSucc
  let Δ := Context.add E (Context.image Formula.raise (Ξ))
  apply Derives.exE (p := E) h2k
  have hZk := ZFContext.under (ZFContext.under hZ D) E
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hd : Derives Δ (instantiateData w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [D, instantiateBody, Formula.raise, instantiateData_rename]) (under hD E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact instantiate_data_unique hZk w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc F.castSucc.castSucc G.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hd hE

theorem abstract_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g F G : Fin m)
     (hw : Derives Γ (omega w)) (h1 : Derives Γ (abstractEnv w a b A B f g)) (h2 : Derives Γ (abstractEnv w a b A B F G)) :
    Derives Γ ((Formula.equal f F).conj (.equal g G)) := by
  let D := abstractBody w a b A B f g
  let Ξ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ h1
  have h2k : Derives Ξ (abstractEnv w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractEnv_rename]) (SyntaxAtomLogic.under_three h2 D)
  let E := abstractBody w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Ξ))))
  apply eliminate_abstract w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc _ h2k
  have hZk := SyntaxAtomLogic.zf_under_three (SyntaxAtomLogic.zf_under_three hZ D) E
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hd : Derives Δ (abstractData w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc) :=
    of_eq (by simp only [D, abstractBody, Formula.raise, abstractData_rename]) (SyntaxAtomLogic.under_three hD E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three (SyntaxAtomLogic.under_three hw D) E)
  exact abstract_data_unique hZk w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) hwk hd hE

end PPAC.Migration.Internal.SyntaxTopEnvironmentUnique
