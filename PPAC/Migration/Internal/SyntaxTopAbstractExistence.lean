import PPAC.Migration.Internal.SyntaxTopInstantiateExistence

/-! AbstractFreeTop的实际完整环境：bound后移；free0取新bound0；其余free取原前驱变量码。 -/
namespace PPAC.Migration.Internal.SyntaxTopAbstractExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f u z n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A b f))
    (hu : Derives Γ (SyntaxVariableTableSyntax.identity false w A b u))
    (hn : Derives Γ (SyntaxMixedImageHead.head w A b z n)) (hB : Derives Γ (successor B b)) :
    Derives Γ (.ex (abstractEnv w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc f.castSucc (Fin.last m))) := by
  let G := SyntaxTermImagePrefixSyntax.prefixed w.castSucc u.castSucc b.castSucc A.castSucc b.castSucc n.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxTermImagePrefixGraph.exists_prefix hZ w u b A b n B hw
    (SyntaxVariableTableUnique.identity_type false w A b u hu) (.conjR (.conjR hn)) hB)
  have hf1 : Derives Δ (SyntaxVariableTableSyntax.shifted true w.castSucc a.castSucc A.castSucc b.castSucc f.castSucc) :=
    of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A b f Fin.castSucc) (under hf G)
  have hu1 : Derives Δ (SyntaxVariableTableSyntax.identity false w.castSucc A.castSucc b.castSucc u.castSucc) :=
    of_eq (SyntaxVariableTableSyntax.identity_rename false w A b u Fin.castSucc) (under hu G)
  have hn1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc A.castSucc b.castSucc z.castSucc n.castSucc) :=
    of_eq (SyntaxMixedImageHead.head_rename w A b z n Fin.castSucc) (under hn G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hh := intro_abstract w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc f.castSucc (Fin.last m) u.castSucc z.castSucc n.castSucc (.conjI hf1 (.conjI hu1 (.conjI hn1 hG)))
  have ho : Derives Δ (.ex (abstractEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)))) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, abstractEnv_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact of_eq (by simp only [Formula.raise, Formula.rename, abstractEnv_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem at_base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f u : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B))
    (hf : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A b f))
    (hu : Derives Γ (SyntaxVariableTableSyntax.identity false w A b u)) :
    Derives Γ (.ex (abstractEnv w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc f.castSucc (Fin.last m))) := by
  let H := SyntaxMixedImageHead.head w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he := SyntaxMixedImageHead.exists_head hZ w a A b hw (.conjL (.conjL hi)) (.conjR (.conjL hi)) (.conjL (.conjR hi))
  apply SyntaxRenameBinders.eliminate_2 H _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, abstractInput_rename]) (SyntaxRenameBinders.under_2 hi H)
  have hf2 : Derives Δ (SyntaxVariableTableSyntax.shifted true w.castSucc.castSucc a.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxVariableTableSyntax.shifted_rename]) (SyntaxRenameBinders.under_2 hf H)
  have hu2 : Derives Δ (SyntaxVariableTableSyntax.identity false w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxVariableTableSyntax.identity_rename]) (SyntaxRenameBinders.under_2 hu H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := at_tables hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc f.castSucc.castSucc u.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hf2 hu2 hH (.conjR (.conjR hi2))
  exact of_eq (by simp only [Formula.raise, Formula.rename, abstractEnv_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem exists_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B)) : Derives Γ (existsAbstract w a b A B) := by
  have hA := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw (.conjL (.conjL hi)) (.conjL (.conjR hi))
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w A b) := .conjI hA (.conjR (.conjL hi))
  let F := SyntaxVariableTableSyntax.shifted true w.castSucc a.castSucc A.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (SyntaxVariableTableExistence.shifted_exists hZ true w a A b hw hctx (.conjL (.conjL hi)) (.conjL (.conjR hi)))
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have hc1 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc A.castSucc b.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w A b Fin.castSucc) (under hctx F)
  let U := SyntaxVariableTableSyntax.identity false w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add U (Context.image Formula.raise Ξ)
  apply Derives.exE (p := U) (SyntaxVariableTableExistence.identity_exists (ZFContext.under hZ F) false w.castSucc A.castSucc b.castSucc hw1 hc1)
  have hZ2 := ZFContext.under (ZFContext.under hZ F) U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 U)
  have hi2 : Derives Δ (abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractInput_rename]) (under (under hi F) U)
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hf2 : Derives Δ (SyntaxVariableTableSyntax.shifted true w.castSucc.castSucc a.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [F, Formula.raise, SyntaxVariableTableSyntax.shifted_rename]) (under hF U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  let G := abstractEnv w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Θ := Context.add G (Context.image Formula.raise Δ)
  apply Derives.exE (p := G) (at_base hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hf2 hU)
  have hG : Derives Θ G := .hyp (Or.inl rfl)
  have ho := intro_abstract_pair w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) hG
  exact of_eq (by simp only [Formula.raise, existsAbstract_rename]) ho
end PPAC.Migration.Internal.SyntaxTopAbstractExistence
