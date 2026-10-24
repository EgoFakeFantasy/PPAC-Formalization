import PPAC.Migration.Internal.ProofTreeNodeForward

/-! 六类载荷、准确局部表与实际子Node构造原node0闭轨迹；无有效父节点假设。 -/
namespace PPAC.Migration.Internal.ProofTreeNodeBackward
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ProofTreeBranchConstruction (shape)

theorem matrix_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6)
    (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (ProofAllNodeSyntax.table test w code)) (hm : Derives Γ (ProofTreeNodeSyntax.matrix test kind w code env)) :
    Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  let s := shape kind
  have hcode := ProofTreeConstructorFacts.range hZ (s.extra+2) s.tag w code env hw (.conjL (.conjR hm))
  have hi := SyntaxForestSyntax.intro_inputs 1 w (fun _ => code) (fun _ => hcode)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => code.castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 1 0 w (fun _ => code) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 := of_eq (ProofTreeNodeSyntax.matrix_rename test kind w code env Fin.castSucc) (under hm B)
  have hl1 := of_eq (ProofAllTableRenaming.table_rename test w code Fin.castSucc) (under hl B)
  have hnat1 := Derives.conjL hm1
  have hp := Derives.impE (.conjR (ProofTreeBranchHead.payload_iff hZ1 s w.castSucc code.castSucc (fun i => (env i).castSucc) hw1 hnat1)) (.conjL (.conjR hm1))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh := Derives.impE (.conjR (ProofTreeBranchHead.node_iff hZ1 s w.castSucc (Fin.last m) code.castSucc (fun i => (env i).castSucc) hw1 hnat1 hp)) (.conjR hB)
  have hpre := Derives.impE (.conjR (ProofTreeChildren.children_iff test hZ1 s.children w.castSucc (fun i => (env i).castSucc) hw1 hnat1)) (.conjR (.conjR hm1))
  have hmat : Derives Δ (ProofTreeTracedStep.matrix test (ObjectProofTree.branch s false) w.castSucc (Fin.last m) (fun i => (env i).castSucc)) :=
    .conjI hh (.conjI HornRuleSyntax.truth_proved hpre)
  have hlocal := Derives.impE (.conjR (ProofTreeNodeTag.local_iff test hZ1 w.castSucc (Fin.last m) code.castSucc hw1 (.conjR hB))) hl1
  have ht := ProofTreeBranchConstruction.intro_branch test hZ1 kind false w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hnat1 hmat hlocal
  have ho : Derives Δ (ProofTreeEntrySyntax.node test w.castSucc code.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [ProofTreeEntrySyntax.node, Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      ProofTreeTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI (.conjR hB) ht
  exact of_eq (ProofTreeEntryFacts.node_rename test w code Fin.castSucc).symm ho

theorem branch_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hl : Derives Γ (ProofAllNodeSyntax.table test w code))
    (hb : Derives Γ (ProofTreeNodeSyntax.branch test kind w code)) : Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  let k := (shape kind).extra+2
  let B := ProofTreeNodeSyntax.body test kind w code
  let Δ := Context.add B (raisedContext k Γ)
  apply HornBinderRules.eliminate_many k B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k hw B)
  have hlN := of_eq (ProofAllTableRenaming.table_rename test w code (old k)) (HornBinderRules.under_body k hl B)
  have ho := matrix_backward test (HornBinderRules.zf_body k hZ B) kind (old k w) (old k code) (slot k) hwN hlN hB
  exact of_eq (ProofTreeEntryFacts.node_rename test w code (old k)).symm ho

theorem node_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ProofTreeNodeSyntax.normalized test w code)) :
    Derives Γ (ProofTreeEntrySyntax.node test w code) := by
  apply ProofTreeRootSyntax.disjoin_elim (ProofTreeRootSyntax.kinds.map (fun kind => ProofTreeNodeSyntax.branch test kind w code)) _ (.conjR hn)
  intro q hq
  obtain ⟨kind,_,rfl⟩ := List.mem_map.mp hq
  apply Derives.impI
  exact branch_backward test (ZFContext.add hZ _) kind w code (add hw _) (add (.conjL hn) _) (.hyp (Or.inl rfl))

theorem node_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((ProofTreeEntrySyntax.node test w code).iff (ProofTreeNodeSyntax.normalized test w code)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact ProofTreeNodeForward.node_forward test (ZFContext.add hZ _) w code (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact node_backward test (ZFContext.add hZ _) w code (add hw _) (.hyp (Or.inl rfl))

theorem root_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code conclusion : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((ProofTreeEntrySyntax.root test w code conclusion).iff
      ((ProofTreeNodeSyntax.normalized test w code).conj (ProofTreeRootSyntax.closedPayload w code conclusion))) :=
  RawCodeFieldAtConstructor.iff_trans (ProofTreeRootBackward.root_iff test hZ w code conclusion hw)
    (FormulaCodeCongruence.conj_congr (node_iff test hZ w code hw) (SyntaxTypeLocalTransfer.iff_refl _))

end PPAC.Migration.Internal.ProofTreeNodeBackward
