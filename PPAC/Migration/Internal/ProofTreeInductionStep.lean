import PPAC.Migration.Internal.ProofTreeInductionChildren

/-! 原六分支在成员IH下实际推出任意对象性质；所有赋值量词在内部消去。 -/
namespace PPAC.Migration.Internal.ProofTreeInductionStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofTreeInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

theorem closure_at {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (w code : Fin m)
    (hc : Derives Γ (closure test P w)) (hn : Derives Γ (.mem code w))
    (hm : Derives Γ (normalized test P w code)) : Derives Γ (property P w code) := by
  have hh : Derives Γ ((Formula.mem code w).imp ((normalized test P w code).imp (property P w code))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, normalized_rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE code hc)
  exact .impE (.impE hh hn) hm

theorem intro_cases {m} {Γ : Context m} (P : Formula 2) (kind : Fin 6) (w code : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hm : Derives Γ (matrix P kind w code env)) :
    Derives Γ (cases P w code) := by
  have hb : Derives Γ (branch P kind w code) := by
    apply HornBinderRules.intro_many ((shape kind).extra+2) (body P kind w code) env
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  exact ProofTreeRootSyntax.disjoin_intro _ _ (List.mem_map.mpr ⟨kind,ProofTreeRootSyntax.kind_mem kind,rfl⟩) hb

theorem matrix_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w)) (hi : Derives Γ (allIH test P w code))
    (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hm : Derives Γ (ProofTreeNodeSyntax.matrix test kind w code env)) : Derives Γ (property P w code) := by
  have hctor := Derives.conjL (Derives.conjR hm)
  have hchildren := ProofTreeInductionChildren.payload_children test P hZ kind w code env hw hi hctor (.conjR (.conjR hm))
  have hp := intro_cases P kind w code env (.conjI (.conjL hm) (.conjI hctor hchildren))
  have hn := ProofTreeConstructorFacts.range hZ ((shape kind).extra+2) (shape kind).tag w code env hw hctor
  exact closure_at test P w code hc hn (.conjI hl hp)

theorem branch_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (kind : Fin 6) (w code : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hi : Derives Γ (allIH test P w code)) (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hb : Derives Γ (ProofTreeNodeSyntax.branch test kind w code)) : Derives Γ (property P w code) := by
  let k := (shape kind).extra+2
  let B := ProofTreeNodeSyntax.body test kind w code
  let Δ := Context.add B (raisedContext k Γ)
  apply HornBinderRules.eliminate_many k B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k hw B)
  have hcN := of_eq (closure_rename test P w (old k)) (HornBinderRules.under_body k hc B)
  have hiN := of_eq (allIH_rename test P w code (old k)) (HornBinderRules.under_body k hi B)
  have hlN := of_eq (ProofAllTableRenaming.table_rename test w code (old k)) (HornBinderRules.under_body k hl B)
  have ho := matrix_step test P (HornBinderRules.zf_body k hZ B) kind (old k w) (old k code) (slot k) hwN hcN hiN hlN hB
  exact of_eq (property_rename P w code (old k)).symm ho

theorem cases_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hi : Derives Γ (allIH test P w code)) (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hs : Derives Γ (ProofTreeNodeSyntax.payloadCases test w code)) : Derives Γ (property P w code) := by
  apply ProofTreeRootSyntax.disjoin_elim (ProofTreeRootSyntax.kinds.map (fun kind => ProofTreeNodeSyntax.branch test kind w code)) _ hs
  intro q hq
  obtain ⟨kind,_,rfl⟩ := List.mem_map.mp hq
  apply Derives.impI
  exact branch_step test P (ZFContext.add hZ _) kind w code (add hw _) (add hc _) (add hi _) (add hl _) (.hyp (Or.inl rfl))

theorem from_induction {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hi : Derives Γ (allIH test P w code)) : Derives Γ (correct test P w code) := by
  apply Derives.impI
  let E := ProofTreeEntrySyntax.node test w code
  have hn := Derives.impE (.conjL (ProofTreeNodeBackward.node_iff test (ZFContext.add hZ E) w code (add hw E))) (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))
  exact cases_step test P (ZFContext.add hZ E) w code (add hw E) (add hc E) (add hi E) (.conjL hn) (.conjR hn)

end PPAC.Migration.Internal.ProofTreeInductionStep
