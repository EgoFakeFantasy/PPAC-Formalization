import PPAC.Migration.Internal.ProjectCompilerRoot

/-! A complete local step independent of the history is accepted by the actual recursive compiler. -/
namespace PPAC.Migration.Internal.ProjectCompilerIndependent
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def allHistories {m} (w n b q : Fin m) : Formula m := .all
  (ProjectCompilerLocalSyntax.localStep w.castSucc b.castSucc q.castSucc (Fin.last m) n.castSucc)

theorem allHistories_rename {m l} (w n b q : Fin m) (ρ : Fin m → Fin l) :
    (allHistories w n b q).rename ρ = allHistories (ρ w) (ρ n) (ρ b) (ρ q) := by
  simp only [allHistories, Formula.rename, ProjectCompilerLocalSyntax.localStep_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem at_history {m} {Γ : Context m} (w n b q h : Fin m) (hl : Derives Γ (allHistories w n b q)) :
    Derives Γ (ProjectCompilerLocalSyntax.localStep w b q h n) := by
  have hi := Derives.allE h hl
  exact of_eq (by simp only [Formula.instantiate, ProjectCompilerLocalSyntax.localStep_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi

theorem compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hl : Derives Γ (allHistories w n b q)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  let B := ProjectCompilerCodeSyntax.carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (ProjectCompilerCodeCarrier.exists_carrier hZ w)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := HornBinderRules.under_body 2 hn B
  have hl2 := of_eq (allHistories_rename w n b q (old 2)) (HornBinderRules.under_body 2 hl B)
  have ho2 := NaturalOrderBasic.ordinal hZ2 w.castSucc.castSucc n.castSucc.castSucc hw2 hn2
  let V := ProjectCompilerEvaluationSyntax.evaluation w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (ProjectCompilerEvaluationExistence.exists_value hZ2 w.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc ho2)
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have ho3 := of_eq (OrdinalSyntax.ordinal_rename n.castSucc.castSucc Fin.castSucc) (under ho2 V)
  have hh := ProjectCompilerHistory.from_value (ZFContext.under hZ2 V) w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) ho3 hV
  let H := (ProjectCompilerRecursionSyntax.graph w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc).conj
    (ProjectCompilerStateSyntax.state w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last (m+2)).castSucc)
  let Θ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hh
  have hH : Derives Θ H := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under (ZFContext.under hZ2 V) H
  have hB4 : Derives Θ (ProjectCompilerCodeSyntax.carrier w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [B, Formula.raise, ProjectCompilerCodeSyntax.carrier_rename] using under (under hB V) H
  have hl4 : Derives Θ (allHistories w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, allHistories_rename, HornBinderSyntax.old] using under (under hl2 V) H
  have hn4 : Derives Θ (.mem n.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := under (under hn2 V) H
  have hv4 := of_eq (ProjectCompilerEvaluationSyntax.evaluation_rename w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) Fin.castSucc) (under hV H)
  have hs := at_history w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) hl4
  have he := ProjectCompilerStateMembership.edge_of_local hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last (m+2)).castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc
    (.conjL hB4) (.conjR hB4) (.conjR hH) hs
  have ht := ProjectCompilerJudgmentSyntax.intro_atCarrier w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hn4
    (ProjectCompilerLocal.context _ _ _ _ _ hs) hv4 he
  have hc := ProjectCompilerCodeSyntax.intro_code w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    n.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hB4 ht
  exact of_eq (by simp only [Formula.raise, ProjectCompilerCodeSyntax.compiled_rename, HornBinderSyntax.old]) hc

end PPAC.Migration.Internal.ProjectCompilerIndependent
