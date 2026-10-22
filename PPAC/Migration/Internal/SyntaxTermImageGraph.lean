import PPAC.Migration.Internal.SyntaxMixedTermUnique

/-! 任意对象总单值且目标项合法的关系，经原Replacement实际构造完整项像表。 -/
namespace PPAC.Migration.Internal.SyntaxTermImageGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open SyntaxTermSyntax (term term_rename contexts contexts_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def outputsTyped {p m} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))).imp
      (term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)))))

theorem outputsTyped_rename {p m k} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) (r : Fin m → Fin k) :
    (outputsTyped P ρ w a c d).rename r = outputsTyped P (fun i => r (ρ i)) (r w) (r a) (r c) (r d) := by
  simp only [outputsTyped, Formula.rename, rel_rename, term_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem outputs_at {p m} {Γ : Context m} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d i q : Fin m)
    (ht : Derives Γ (outputsTyped P ρ w a c d)) :
    Derives Γ (((Formula.mem i a).conj (rel P ρ i q)).imp (term w c d q)) :=
  of_eq (by simp only [Formula.instantiate, Formula.rename, rel_rename, term_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i ht))

theorem natural_outputs {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (p+2)) (ρ : Fin p → Fin m)
    (w a c d : Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (outputsTyped P ρ w a c d)) :
    Derives Γ (RelationGraph.outputsInto P ρ a w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ht2 : Derives Δ (outputsTyped P (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, outputsTyped_rename]) (SyntaxRenameBinders.under_2 ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := Derives.impE (outputs_at P _ w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) ht2) hB
  exact SyntaxTerms.range (SyntaxRenameBinders.zf_under_2 hZ B) _ _ _ _ hw2 hc

theorem from_graph {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (p+2)) (ρ : Fin p → Fin m)
    (w a c d f : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hcd : Derives Γ (contexts w c d))
    (ht : Derives Γ (outputsTyped P ρ w a c d)) (hf : Derives Γ (RelationGraphSyntax.functionGraph P ρ a f)) :
    Derives Γ (imageMap w f a c d) := by
  apply Derives.conjI ha
  apply Derives.conjI hcd
  apply Derives.conjI (RelationGraph.sequence P ρ a w f hf (natural_outputs hZ P ρ w a c d hw ht))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have ht2 : Derives Δ (outputsTyped P (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, outputsTyped_rename]) (SyntaxRenameBinders.under_2 ht E)
  have hf2 : Derives Δ (RelationGraphSyntax.functionGraph P (paramsUp (paramsUp ρ)) a.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, RelationGraphSyntax.functionGraph_rename]) (SyntaxRenameBinders.under_2 hf E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hl := RelationGraphSyntax.law_at P _ a.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hf2)
  have hv := Derives.impE (.conjL hl) hE
  exact Derives.impE (outputs_at P _ w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) ht2) hv

theorem exists_image {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (p+2)) (ρ : Fin p → Fin m)
    (w a c d : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hcd : Derives Γ (contexts w c d))
    (hF : Derives Γ (ReplacementPredicates.total P ρ a)) (ht : Derives Γ (outputsTyped P ρ w a c d)) :
    Derives Γ (.ex ((imageMap w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc).conj
      (RelationGraphSyntax.functionGraph P (paramsUp ρ) a.castSucc (Fin.last m)))) := by
  let G := RelationGraphSyntax.functionGraph P (paramsUp ρ) a.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (RelationGraphFunction.exists_graph hZ P ρ a hF)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hcd1 : Derives Δ (contexts w.castSucc c.castSucc d.castSucc) := of_eq (contexts_rename w c d Fin.castSucc) (under hcd G)
  have ht1 : Derives Δ (outputsTyped P (paramsUp ρ) w.castSucc a.castSucc c.castSucc d.castSucc) :=
    of_eq (by simp only [Formula.raise, outputsTyped_rename]) (under ht G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hm := from_graph (ZFContext.under hZ G) P (paramsUp ρ) w.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) hw1 (under ha G) hcd1 ht1 hG
  have ho : Derives Δ (.ex ((imageMap w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc).conj
      (RelationGraphSyntax.functionGraph P (paramsUp (paramsUp ρ)) a.castSucc.castSucc (Fin.last (m+1))))) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [G, Formula.instantiate, Formula.rename, imageMap_rename, RelationGraphSyntax.functionGraph_rename,
      paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hm hG)
  exact of_eq (by simp only [Formula.raise, Formula.rename, imageMap_rename, RelationGraphSyntax.functionGraph_rename,
    paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

end PPAC.Migration.Internal.SyntaxTermImageGraph
