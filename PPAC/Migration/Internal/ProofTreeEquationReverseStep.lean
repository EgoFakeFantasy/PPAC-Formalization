import PPAC.Migration.Internal.ProofTreeEquationSyntax

/-! 反向对象成员IH把P子节点化为真实Node，六类赋值块与方程见证均对象消去。 -/
namespace PPAC.Migration.Internal.ProofTreeEquationReverseStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofTreeInductionSyntax ProofTreeEquationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

theorem ih_at {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (w code child : Fin m)
    (hi : Derives Γ (reverseIH test P w code)) (hm : Derives Γ (.mem child code))
    (hp : Derives Γ (property P w child)) : Derives Γ (ProofTreeEntrySyntax.node test w child) := by
  have hh : Derives Γ ((Formula.mem child code).imp (reverseCorrect test P w child)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, reverseCorrect_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE child hi)
  exact .impE (.impE hh hm) hp

theorem children_to_nodes {m a} {Γ : Context m} (test : Formula 1) (P : Formula 2) (is : List (Fin a))
    (w code : Fin m) (env : Fin a → Fin m) (hi : Derives Γ (reverseIH test P w code))
    (hb : ∀ i, i ∈ is → Derives Γ (.mem (env i) code))
    (hp : Derives Γ (children P is w env)) : Derives Γ (ProofTreeChildren.children test is w env) := by
  induction is with
  | nil => exact HornRuleSyntax.truth_proved
  | cons i is ih =>
    exact .conjI (ih_at test P w code (env i) hi (hb i List.mem_cons_self) (.conjL hp))
      (ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (.conjR hp))

theorem matrix_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (reverseIH test P w code))
    (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hm : Derives Γ (matrix P kind w code env)) : Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  have hctor := Derives.conjL (Derives.conjR hm)
  have hn := children_to_nodes test P (shape kind).children w code env hi
    (fun i _ => ProofTreeNodeSyntax.payload_field_below hZ kind w code env i hw hctor) (.conjR (.conjR hm))
  have hs := ProofTreeNodeSyntax.intro_cases test kind w code env (.conjI (.conjL hm) (.conjI hctor hn))
  exact ProofTreeNodeBackward.node_backward test hZ w code hw (.conjI hl hs)

theorem branch_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (kind : Fin 6) (w code : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (reverseIH test P w code)) (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hb : Derives Γ (branch P kind w code)) : Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  let k := (shape kind).extra+2
  let B := body P kind w code
  let Δ := Context.add B (raisedContext k Γ)
  apply HornBinderRules.eliminate_many k B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k hw B)
  have hiN := of_eq (reverseIH_rename test P w code (old k)) (HornBinderRules.under_body k hi B)
  have hlN := of_eq (ProofAllTableRenaming.table_rename test w code (old k)) (HornBinderRules.under_body k hl B)
  have ho := matrix_step test P (HornBinderRules.zf_body k hZ B) kind (old k w) (old k code) (slot k) hwN hiN hlN hB
  exact of_eq (ProofTreeEntryFacts.node_rename test w code (old k)).symm ho

theorem cases_step {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hi : Derives Γ (reverseIH test P w code))
    (hl : Derives Γ (ProofAllNodeSyntax.table test w code)) (hs : Derives Γ (cases P w code)) :
    Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  apply ProofTreeRootSyntax.disjoin_elim (ProofTreeRootSyntax.kinds.map (fun kind => branch P kind w code)) _ hs
  intro q hq
  obtain ⟨kind,_,rfl⟩ := List.mem_map.mp hq
  apply Derives.impI
  exact branch_step test P (ZFContext.add hZ _) kind w code (add hw _) (add hi _) (add hl _) (.hyp (Or.inl rfl))

theorem from_induction {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w))
    (hi : Derives Γ (reverseIH test P w code)) : Derives Γ (reverseCorrect test P w code) := by
  apply Derives.impI
  let E := property P w code
  have hn := Derives.impE (.conjL (equation_at test P w code (add he E))) (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))
  exact cases_step test P (ZFContext.add hZ E) w code (add hw E) (add hi E) (.conjL hn) (.conjR hn)

end PPAC.Migration.Internal.ProofTreeEquationReverseStep
