import PPAC.Migration.Internal.SchemaIndexScopes
import PPAC.Migration.Internal.SyntaxMapCodeExistence

/-! Every actual schema embedding obtains its original complete natural-list code. -/
namespace PPAC.Migration.Internal.SchemaIndexCoded
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem intro_coded_state {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g R : Fin m)
    (hs : Derives Γ (codedState site w n scopes g R)) : Derives Γ (existsCodedState site w n) := by
  apply HornBinderRules.intro_many 6 (codedBody site w n) (Fin.lastCases R (Fin.lastCases g scopes))
  exact of_eq (by simp only [codedBody, codedState_rename, assign_old, assign_slot, Fin.lastCases_last, Fin.lastCases_castSucc]) hs

theorem exists_at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (state site w n scopes g)) : Derives Γ (existsCodedState site w n) := by
  have hm := SchemaIndexFacts.graph_map site w n scopes g (.conjR hs)
  let K := SyntaxMapCodeSyntax.encoded w.castSucc g.castSucc (sourceScope site scopes).castSucc (targetScope site scopes).castSucc (Fin.last m)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) (SyntaxMapCodeExistence.exists_code hZ w g (sourceScope site scopes) (targetScope site scopes) hw hm)
  have hs1 := of_eq (state_rename site w n scopes g Fin.castSucc) (under hs K)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have he : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc g.castSucc
      (sourceScope site (fun i => (scopes i).castSucc)) (targetScope site (fun i => (scopes i).castSucc)) (Fin.last m)) :=
    of_eq (by rw [sourceScope_map, targetScope_map]) hK
  have ho := intro_coded_state site w.castSucc n.castSucc (fun i => (scopes i).castSucc) g.castSucc (Fin.last m) (.conjI hs1 he)
  exact of_eq (existsCodedState_rename site w n Fin.castSucc).symm ho

theorem exists_coded_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsCodedState site w n) := by
  let B := stateBody site w n
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ (SchemaIndexScopes.exists_state hZ site w n hw hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have ho := exists_at_state (HornBinderRules.zf_body 5 hZ B) site (old 5 w) (old 5 n)
    (fun i => slot 5 i.castSucc) (slot 5 (Fin.last 4)) hw5 hB
  exact of_eq (existsCodedState_rename site w n (old 5)).symm ho

end PPAC.Migration.Internal.SchemaIndexCoded
