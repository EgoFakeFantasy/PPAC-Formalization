import PPAC.Migration.Internal.SchemaIndexTail
import PPAC.Migration.Internal.SchemaIndexRenameSystem

/-! The two collection embeddings fix the second head, including all candidate outputs. -/
namespace PPAC.Migration.Internal.SchemaIndexHead
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem matrix_one_fixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (image : Bool) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m) (p : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes))
    (hm : Derives Γ (SchemaIndexSyntax.matrix (if image then 2 else 1) w n scopes g env))
    (hp : Derives Γ (SyntaxNumeralSyntax.numeral 1 p)) : Derives Γ (edge g p p) := by
  let Z := (empty (Fin.last m)).conj (successor p.castSucc (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ 0 p _ hp
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn Z
  have hc1 := of_eq (chain_rename n scopes Fin.castSucc) (under hc Z)
  have hm1 := of_eq (matrix_rename (if image then 2 else 1) w n scopes g env Fin.castSucc) (under hm Z)
  have hE : Derives Δ Z := .hyp (Or.inl rfl)
  have hz := Derives.conjL hE
  have hs := Derives.conjR hE
  have hk := SyntaxIndexLiftOrder.zero_member hZ1 w.castSucc n.castSucc (scopes 0).castSucc (Fin.last m) hw1 hn1 (.conjL hc1) hz
  cases image with
  | false =>
    have h0 := SyntaxIndexLiftEdges.zero_iff hZ1 w.castSucc (env 0).castSucc n.castSucc (scopes 0).castSucc (scopes 0).castSucc (scopes 1).castSucc (env 1).castSucc (Fin.last m) (Fin.last m) hw1 (.conjL (.conjR hm1)) hz
    have he := Derives.impE (.conjR h0) hz
    have h1 := SyntaxIndexLiftEdges.successor_iff hZ1 w.castSucc (env 1).castSucc (scopes 0).castSucc (scopes 1).castSucc (scopes 1).castSucc (scopes 2).castSucc g.castSucc p.castSucc p.castSucc (Fin.last m) (Fin.last m) hw1 (.conjR (.conjR hm1)) hk hs hs
    exact of_eq (edge_rename g p p Fin.castSucc).symm (Derives.impE (.conjR h1) he)
  | true =>
    have h0 := SyntaxIndexLiftEdges.zero_iff hZ1 w.castSucc (env 0).castSucc n.castSucc (scopes 1).castSucc (scopes 0).castSucc (scopes 2).castSucc (env 1).castSucc (Fin.last m) (Fin.last m) hw1 (.conjL (.conjR hm1)) hz
    have he := Derives.impE (.conjR h0) hz
    have h1 := SyntaxIndexLiftEdges.successor_iff hZ1 w.castSucc (env 1).castSucc (scopes 0).castSucc (scopes 2).castSucc (scopes 1).castSucc (scopes 3).castSucc g.castSucc p.castSucc p.castSucc (Fin.last m) (Fin.last m) hw1 (.conjR (.conjR hm1)) hk hs hs
    exact of_eq (edge_rename g p p Fin.castSucc).symm (Derives.impE (.conjR h1) he)

theorem one_fixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (image : Bool) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g p : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (state (if image then 2 else 1) w n scopes g)) (hp : Derives Γ (SyntaxNumeralSyntax.numeral 1 p)) : Derives Γ (edge g p p) := by
  let B := body (if image then 2 else 1) w n scopes g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (Derives.conjR hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (.mem (old 2 n) (old 2 w)) := HornBinderRules.under_body 2 hn B
  have hc2 := of_eq (chain_rename n scopes (old 2)) (HornBinderRules.under_body 2 (.conjL hs) B)
  have hp2 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 p (old 2)) (HornBinderRules.under_body 2 hp B)
  have ho := matrix_one_fixed (HornBinderRules.zf_body 2 hZ B) image (old 2 w) (old 2 n) (fun i => old 2 (scopes i))
    (old 2 g) (slot 2) (old 2 p) hw2 hn2 hc2 hB hp2
  exact of_eq (edge_rename g p p (old 2)).symm ho

theorem edge_output_subst {m} {Γ : Context m} (g p q y : Fin m) (he : Derives Γ (.equal q y))
    (hq : Derives Γ (edge g p q)) : Derives Γ (edge g p y) := by
  let P := edge g.castSucc p.castSucc (Fin.last m)
  have h0 : P.instantiate q = edge g p q := by simp only [P, Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate y = edge g p y := by simp only [P, Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hq))

theorem one_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (image : Bool) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g p y : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (state (if image then 2 else 1) w n scopes g)) (hp : Derives Γ (SyntaxNumeralSyntax.numeral 1 p)) :
    Derives Γ ((edge g p y).iff (.equal y p)) := by
  have he := one_fixed hZ image w n scopes g p hw hn hs hp
  have hm := SchemaIndexFacts.graph_map (if image then 2 else 1) w n scopes g (.conjR hs)
  apply Derives.conjI
  · apply Derives.impI
    exact GraphProperties.single_valued g (sourceScope (if image then 2 else 1) scopes) p y p
      (add (ZFContext.arithmetic hZ).base.extensionality _) (add (.conjL (.conjR hm)) _) (.hyp (Or.inl rfl)) (add he _)
  · apply Derives.impI
    exact edge_output_subst g p p y (eq_symm (.hyp (Or.inl rfl))) (add he _)

end PPAC.Migration.Internal.SchemaIndexHead
