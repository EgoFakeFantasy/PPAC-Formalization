import PPAC.Migration.Internal.SchemaIndexFacts

/-! All four genuine scope successors and the final schema graph are object witnesses. -/
namespace PPAC.Migration.Internal.SchemaIndexScopes
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem intro_state {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m)
    (hs : Derives Γ (state site w n scopes g)) : Derives Γ (existsState site w n) := by
  apply HornBinderRules.intro_many 5 (stateBody site w n) (Fin.lastCases g scopes)
  exact of_eq (by simp only [stateBody, state_rename, assign_old, assign_slot, Fin.lastCases_last, Fin.lastCases_castSucc]) hs

theorem exists_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsState site w n) := by
  let B0 := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) n.castSucc)
  let Γ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) (Derives.impE (OmegaSyntax.step_at w n (.conjL hw)) hn)
  have h0 : Derives Γ1 B0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B0)
  let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Γ2 := Context.add B1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := B1) (Derives.impE (OmegaSyntax.step_at w.castSucc (Fin.last m) (.conjL hw1)) (.conjL h0))
  have h1 : Derives Γ2 B1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 B1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
  let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+2)) (Fin.last (m+1)).castSucc)
  let Γ3 := Context.add B2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := B2) (Derives.impE (OmegaSyntax.step_at w.castSucc.castSucc (Fin.last (m+1)) (.conjL hw2)) (.conjL h1))
  have h2 : Derives Γ3 B2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 B2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
  let B3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+3)) (Fin.last (m+2)).castSucc)
  let Γ4 := Context.add B3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := B3) (Derives.impE (OmegaSyntax.step_at w.castSucc.castSucc.castSucc (Fin.last (m+2)) (.conjL hw3)) (.conjL h2))
  have h3 : Derives Γ4 B3 := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 B3
  have hw4 := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 B3)
  have hs0 : Derives Γ4 (successor (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under (under (.conjR h0) B1) B2) B3)
  have hs1 : Derives Γ4 (successor (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under (.conjR h1) B2) B3)
  have hs2 : Derives Γ4 (successor (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (.conjR h2) B3)
  have hs3 : Derives Γ4 (successor (Fin.last (m+3)) (Fin.last (m+2)).castSucc) := of_eq (by rfl) (.conjR h3)
  let scopes : Fin 4 → Fin (m+4) := Fin.cases (Fin.last m).castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+1)).castSucc.castSucc (Fin.cases (Fin.last (m+2)).castSucc (fun _ => (Fin.last (m+3)))))
  have hc : Derives Γ4 (chain n.castSucc.castSucc.castSucc.castSucc scopes) := .conjI hs0 (.conjI hs1 (.conjI hs2 hs3))
  let G := graph site w.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc
    (fun i => (scopes i).castSucc) (Fin.last (m+4))
  let Γ5 := Context.add G (Context.image Formula.raise Γ4)
  have hn4 : Derives Γ4 (.mem n.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) :=
    under (under (under (under hn B0) B1) B2) B3
  apply Derives.exE (p := G) (SchemaIndexGraphExistence.exists_graph hZ4 site w.castSucc.castSucc.castSucc.castSucc
    n.castSucc.castSucc.castSucc.castSucc scopes hw4 hn4 hc)
  have hc5 := of_eq (chain_rename n.castSucc.castSucc.castSucc.castSucc scopes Fin.castSucc) (under hc G)
  have hG : Derives Γ5 G := .hyp (Or.inl rfl)
  have ho := intro_state site w.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc
    (fun i => (scopes i).castSucc) (Fin.last (m+4)) (.conjI hc5 hG)
  exact of_eq (by simp only [Formula.raise, existsState_rename]) ho

end PPAC.Migration.Internal.SchemaIndexScopes
