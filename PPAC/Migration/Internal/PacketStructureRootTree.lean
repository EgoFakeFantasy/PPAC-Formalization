import PPAC.Migration.Internal.PacketStructureRootWitness

/-! All eight original tree witnesses align with the specified tree input, tail and output. -/
namespace PPAC.Migration.Internal.PacketStructureRootTree
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureRootSyntax PacketStructureRootTransport
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (treeRow w n t a r))
    (ho : Derives Γ (PacketStructureApplicationSyntax.outcome .tree w V r)) : Derives Γ (treeCase w V n t a) := by
  let L := PacketStructureRootWitness.treeWitness w V r
  let Δ := Context.add L (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 L _ (of_eq (PacketStructureRootWitness.actual_tree_witness w V r) ho)
  have hZ8 := HornBinderRules.zf_body 8 hZ L
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw L)
  have hr8 := of_eq (treeRow_rename w n t a r (old 8)) (HornBinderRules.under_body 8 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR hL
  have he (i : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ8 3 3 3 (old 8 w)
    (SyntaxAtomSyntax.three (slot 8 7) (slot 8 2) (slot 8 3)) (SyntaxAtomSyntax.three (old 8 n) (old 8 t) (old 8 a))
    (old 8 r) i hw8 (.conjL hA) hr8
  have hraw := StructuralNodeSyntax.output_subst (old 8 w) (slot 8 0) (slot 8 1) (slot 8 7) (old 8 n) (he 0) (.conjL hL)
  have hp := Derives.conjR hA
  have hf := forest_tail (old 8 w) (old 8 V) (slot 8 1) (slot 8 4) (slot 8 2) (slot 8 5) (old 8 t) (he 1) (.conjL hp)
  have ht := PacketTokenRootTransport.entry_third 2 (old 8 w) (old 8 V) (slot 8 0) (slot 8 6) (slot 8 3) (old 8 a) (he 2) (.conjR (.conjR hp))
  exact of_eq (treeCase_rename w V n t a (old 8)).symm
    (PacketStructureRootSyntax.intro_tree (old 8 w) (old 8 V) (old 8 n) (old 8 t) (old 8 a)
      (slot 8 0) (slot 8 1) (slot 8 4) (slot 8 5) (slot 8 6) hraw hf (.conjL (.conjR hp)) ht)

theorem backward {m} {Γ : Context m} (w V n t a r : Fin m) (hr : Derives Γ (treeRow w n t a r))
    (hc : Derives Γ (treeCase w V n t a)) : Derives Γ (PacketStructureApplicationSyntax.outcome .tree w V r) := by
  let L := treeCaseBody w V n t a
  let Δ := Context.add L (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 L _ hc
  have hr5 := of_eq (treeRow_rename w n t a r (old 5)) (HornBinderRules.under_body 5 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  let env : Fin 7 → Fin (m+5) := Fin.cases (slot 5 0) (Fin.cases (slot 5 1) (Fin.cases (old 5 t) (Fin.cases (old 5 a)
    (Fin.cases (slot 5 2) (Fin.cases (slot 5 3) (Fin.cases (slot 5 4) Fin.elim0))))))
  have ha : Derives Δ (treeAt (old 5 w) (old 5 V) (old 5 r) (old 5 n) env) := .conjI hr5 (.conjR hL)
  have hl := PacketStructureLocalSyntax.intro_tree (old 5 w) (old 5 V) (old 5 r) (old 5 n) env (.conjL hL) ha
  exact of_eq (PacketStructureApplicationSyntax.outcome_rename .tree w V r (old 5)).symm
    (PacketStructureApplicationSyntax.intro_outcome .tree (old 5 w) (old 5 V) (old 5 r) env hl)

theorem root_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (treeRow w n t a r)) :
    Derives Γ ((PacketStructureApplicationSyntax.outcome .tree w V r).iff (treeCase w V n t a)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w V n t a r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w V n t a r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureRootTree
