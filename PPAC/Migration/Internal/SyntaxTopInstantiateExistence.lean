import PPAC.Migration.Internal.SyntaxTopEnvironmentSyntax

/-! 每个合法内部目标项及源bound后继，实际取得InstantiateTop的两张完整环境表。 -/
namespace PPAC.Migration.Internal.SyntaxTopInstantiateExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t u g : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t))
    (hu : Derives Γ (SyntaxVariableTableSyntax.identity true w a b u))
    (hg : Derives Γ (SyntaxVariableTableSyntax.identity false w a b g)) :
    Derives Γ (.ex (instantiateEnv w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc (Fin.last m) g.castSucc)) := by
  let F := SyntaxTermImagePrefixSyntax.prefixed w.castSucc u.castSucc a.castSucc a.castSucc b.castSucc t.castSucc A.castSucc (Fin.last m)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  have he := SyntaxTermImagePrefixGraph.exists_prefix hZ w u a a b t A hw
    (SyntaxVariableTableUnique.identity_type true w a b u hu) (.conjL hi) (.conjR hi)
  apply Derives.exE (p := F) he
  have hu1 : Derives Δ (SyntaxVariableTableSyntax.identity true w.castSucc a.castSucc b.castSucc u.castSucc) :=
    of_eq (SyntaxVariableTableSyntax.identity_rename true w a b u Fin.castSucc) (under hu F)
  have hg1 : Derives Δ (SyntaxVariableTableSyntax.identity false w.castSucc a.castSucc b.castSucc g.castSucc) :=
    of_eq (SyntaxVariableTableSyntax.identity_rename false w a b g Fin.castSucc) (under hg F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hh := intro_instantiate w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc (Fin.last m) g.castSucc u.castSucc (.conjI hu1 (.conjI hF hg1))
  have ho : Derives Δ (.ex (instantiateEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) g.castSucc.castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, instantiateEnv_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact of_eq (by simp only [Formula.raise, Formula.rename, instantiateEnv_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem exists_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t)) :
    Derives Γ (existsInstantiate w a b A t) := by
  have hc := Derives.conjL (.conjL hi)
  let U := SyntaxVariableTableSyntax.identity true w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) (SyntaxVariableTableExistence.identity_exists hZ true w a b hw hc)
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hc1 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc a.castSucc b.castSucc) :=
    of_eq (SyntaxTermSyntax.contexts_rename w a b Fin.castSucc) (under hc U)
  let G := SyntaxVariableTableSyntax.identity false w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add G (Context.image Formula.raise Ξ)
  apply Derives.exE (p := G) (SyntaxVariableTableExistence.identity_exists (ZFContext.under hZ U) false w.castSucc a.castSucc b.castSucc hw1 hc1)
  have hZ2 := ZFContext.under (ZFContext.under hZ U) G
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 G)
  have hi2 : Derives Δ (instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, instantiateInput_rename]) (under (under hi U) G)
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hu2 : Derives Δ (SyntaxVariableTableSyntax.identity true w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [U, Formula.raise, SyntaxVariableTableSyntax.identity_rename]) (under hU G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  let F := instantiateEnv w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc
  let Θ := Context.add F (Context.image Formula.raise Δ)
  apply Derives.exE (p := F) (at_tables hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hu2 hG)
  have hF : Derives Θ F := .hyp (Or.inl rfl)
  have ho := intro_instantiate_pair w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hF
  exact of_eq (by simp only [Formula.raise, existsInstantiate_rename]) ho
end PPAC.Migration.Internal.SyntaxTopInstantiateExistence
