import PPAC.Migration.Internal.FixedAxiomPacketExistence

/-! 全内部叶包候选的唯一性、异标签互斥与自然范围；六槽证书均对象消去。 -/
namespace PPAC.Migration.Internal.FixedAxiomPacketUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax FixedAxiomPacketSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix NaturalMultiplicationSyntax.product NaturalAdditionSyntax.sum SyntaxNumeralSyntax.numeral

theorem unique_at_matrix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w p q : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf tag w p))
    (hq : Derives Γ (FixedAxiomPacketSyntax.matrix tag w q env)) : Derives Γ (.equal p q) := by
  let B := body tag w p
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hp
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  have hqN := of_eq (matrix_rename tag w q env (old 6)) (HornBinderRules.under_body 6 hq B)
  exact FixedAxiomPacketFacts.matrix_unique (HornBinderRules.zf_body 6 hZ B) tag (old 6 w) (old 6 p) (old 6 q) (slot 6) (fun i => old 6 (env i)) hwN hB hqN

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf tag w p)) (hq : Derives Γ (leaf tag w q)) : Derives Γ (.equal p q) := by
  let B := body tag w q
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  have hpN := of_eq (leaf_rename tag w p (old 6)) (HornBinderRules.under_body 6 hp B)
  exact unique_at_matrix (HornBinderRules.zf_body 6 hZ B) tag (old 6 w) (old 6 p) (old 6 q) (slot 6) hwN hpN hB

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf tag w p)) : Derives Γ (.mem p w) := by
  let B := body tag w p
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hp
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  exact FixedAxiomPacketFacts.matrix_range (HornBinderRules.zf_body 6 hZ B) tag (old 6 w) (old 6 p) (slot 6) hwN hB

theorem reject_at_matrix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (hkl : k ≠ l)
    (w p : Fin m) (env : Fin 6 → Fin m) (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf k w p))
    (hq : Derives Γ (FixedAxiomPacketSyntax.matrix l w p env)) : Derives Γ .bot := by
  let B := body k w p
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hp
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ6 := HornBinderRules.zf_body 6 hZ B
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  have hqN := of_eq (matrix_rename l w p env (old 6)) (HornBinderRules.under_body 6 hq B)
  have he := FixedAxiomPacketFacts.matrix_tag_equal hZ6 k l (old 6 w) (old 6 p) (slot 6) (fun i => old 6 (env i)) hwN hB hqN
  exact .impE (SyntaxNumerals.different hZ6 k l hkl (slot 6 1) (old 6 (env 1))
    (FixedAxiomPacketFacts.field1 k (old 6 w) (old 6 p) (slot 6) hB)
    (FixedAxiomPacketFacts.field1 l (old 6 w) (old 6 p) (fun i => old 6 (env i)) hqN)) he

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (hkl : k ≠ l)
    (w p : Fin m) (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf k w p)) (hq : Derives Γ (leaf l w p)) : Derives Γ .bot := by
  let B := body l w p
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  have hpN := of_eq (leaf_rename k w p (old 6)) (HornBinderRules.under_body 6 hp B)
  exact reject_at_matrix (HornBinderRules.zf_body 6 hZ B) k l hkl (old 6 w) (old 6 p) (slot 6) hwN hpN hB

theorem output_subst {m} {Γ : Context m} (tag : Nat) (w p q : Fin m)
    (he : Derives Γ (.equal p q)) (hp : Derives Γ (leaf tag w p)) : Derives Γ (leaf tag w q) := by
  let P := leaf tag w.castSucc (Fin.last m)
  have h0 : P.instantiate p = leaf tag w p := by simp only [P, Formula.instantiate, leaf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate q = leaf tag w q := by simp only [P, Formula.instantiate, leaf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (leaf tag w p)) :
    Derives Γ ((leaf tag w q).iff (.equal q p)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact unique (ZFContext.add hZ _) tag w q p (add hw _) (.hyp (Or.inl rfl)) (add hp _)
  · apply Derives.impI
    exact output_subst tag w p q (eq_symm (.hyp (Or.inl rfl))) (add hp _)

end PPAC.Migration.Internal.FixedAxiomPacketUnique
