import PPAC.Migration.Internal.PacketStructureLocalSyntax

/-! Structural payload, zero, successor and unit witnesses are constructed and discharged in the original object theory. -/
namespace PPAC.Migration.Internal.PacketStructureLocal
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketStructureSyntax PacketStructureLocalSyntax PacketStructureRuleData
open SyntaxRenameQuerySyntax (of_eq)

theorem tree_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix treeRule w r V env)) : Derives Γ (treeLocal w V r env) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralNodeSyntax.raw w.castSucc (env 0).castSucc (env 1).castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (StructuralNodeExistence.exists_raw hZ w (env 0) (env 1) hw (environmentNat_at w env hn 0) (environmentNat_at w env hn 1))
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 7 w env Fin.castSucc) (under hn P)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename treeRule w r V env Fin.castSucc) (under hm P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketStructureMatrix.tree_at (ZFContext.under hZ P) w.castSucc V.castSucc r.castSucc
    (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hP))) hm1
  exact of_eq (treeLocal_rename w V r env Fin.castSucc).symm
    (intro_tree w.castSucc V.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) (.conjR hP) ha)

theorem nil_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix nilRule w r V env)) : Derives Γ (nilLocal w V r env) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 U _ (StructuralListUnits.exists_units w hw)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw U)
  have hn2 := of_eq (environmentNat_rename 1 w env (old 2)) (HornBinderRules.under_body 2 hn U)
  have hm2 := of_eq (HornRuleSyntax.matrix_rename nilRule w r V env (old 2)) (HornBinderRules.under_body 2 hm U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketStructureMatrix.nil_at (HornBinderRules.zf_body 2 hZ U) (old 2 w) (old 2 r)
    (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) (old 2 V) hw2 hn2 (.conjL hU) (.conjR hU))) hm2
  exact of_eq (nilLocal_rename w V r env (old 2)).symm
    (intro_nil (old 2 w) (old 2 V) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) (.conjL hU) (.conjR hU) ha)

theorem cons_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix consRule w r V env)) : Derives Γ (consLocal w V r env) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc (env 0).castSucc (env 1).castSucc (Fin.last m))
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (StructuralConsCore.exists_cons hZ w (env 0) (env 1) hw (environmentNat_at w env hn 0) (environmentNat_at w env hn 1))
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (under hn P)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename consRule w r V env Fin.castSucc) (under hm P)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (env 2).castSucc.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (OriginalBinderStepSyntax.successor_exists w.castSucc (env 2).castSucc hw1 (environmentNat_at _ _ hn1 2))
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hn2 := of_eq (environmentNat_rename 6 w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 Q)
  have hm2 := of_eq (HornRuleSyntax.matrix_rename consRule w.castSucc r.castSucc V.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hm1 Q)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc (env 0).castSucc (env 1).castSucc (Fin.last m) Fin.castSucc) (under (.conjR hP) Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketStructureMatrix.cons_at (ZFContext.under hZ1 Q) w.castSucc.castSucc V.castSucc.castSucc r.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) hw2 hn2 hc2 (.conjR hQ))) hm2
  have ho := intro_cons w.castSucc.castSucc V.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (fun i => (env i).castSucc.castSucc) hc2 (.conjR hQ) ha
  simpa only [Formula.raise,consLocal_rename] using ho

theorem packet_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix packetRule w r V env)) : Derives Γ (packetLocal w V r env) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn P)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename packetRule w r V env Fin.castSucc) (under hm P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketStructureMatrix.packet_at (ZFContext.under hZ P) w.castSucc V.castSucc r.castSucc
    (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hP))) hm1
  exact of_eq (packetLocal_rename w V r env Fin.castSucc).symm
    (intro_packet w.castSucc V.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) (.conjR hP) ha)

theorem tree_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hl : Derives Γ (treeLocal w V r env)) : Derives Γ (HornRuleSyntax.matrix treeRule w r V env) := by
  let L := treeBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hnk := of_eq (environmentNat_rename 7 w env (old 1)) (HornBinderRules.under_body 1 hn L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename treeRule w r V env (old 1)).symm
    (.impE (.conjR (PacketStructureMatrix.tree_at (HornBinderRules.zf_body 1 hZ L) (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)) hwk hnk (.conjL hL))) (.conjR hL))

theorem tree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((HornRuleSyntax.matrix treeRule w r V env).iff (treeLocal w V r env)) := by
  apply Derives.conjI
  · exact .impI (tree_forward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))
  · exact .impI (tree_backward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))

theorem nil_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hl : Derives Γ (nilLocal w V r env)) : Derives Γ (HornRuleSyntax.matrix nilRule w r V env) := by
  let L := nilBody w V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hnk := of_eq (environmentNat_rename 1 w env (old 2)) (HornBinderRules.under_body 2 hn L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename nilRule w r V env (old 2)).symm
    (.impE (.conjR (PacketStructureMatrix.nil_at (HornBinderRules.zf_body 2 hZ L) (old 2 w) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) (old 2 V) hwk hnk (.conjL hL) (.conjL (.conjR hL)))) (.conjR (.conjR hL)))

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env)) :
    Derives Γ ((HornRuleSyntax.matrix nilRule w r V env).iff (nilLocal w V r env)) := by
  apply Derives.conjI
  · exact .impI (nil_forward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))
  · exact .impI (nil_backward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))

theorem cons_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hl : Derives Γ (consLocal w V r env)) : Derives Γ (HornRuleSyntax.matrix consRule w r V env) := by
  let L := consBody w V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hnk := of_eq (environmentNat_rename 6 w env (old 2)) (HornBinderRules.under_body 2 hn L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename consRule w r V env (old 2)).symm
    (.impE (.conjR (PacketStructureMatrix.cons_at (HornBinderRules.zf_body 2 hZ L) (old 2 w) (old 2 V) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) hwk hnk (.conjL hL) (.conjL (.conjR hL)))) (.conjR (.conjR hL)))

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) :
    Derives Γ ((HornRuleSyntax.matrix consRule w r V env).iff (consLocal w V r env)) := by
  apply Derives.conjI
  · exact .impI (cons_forward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))
  · exact .impI (cons_backward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))

theorem packet_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hl : Derives Γ (packetLocal w V r env)) : Derives Γ (HornRuleSyntax.matrix packetRule w r V env) := by
  let L := packetBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hnk := of_eq (environmentNat_rename 3 w env (old 1)) (HornBinderRules.under_body 1 hn L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename packetRule w r V env (old 1)).symm
    (.impE (.conjR (PacketStructureMatrix.packet_at (HornBinderRules.zf_body 1 hZ L) (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)) hwk hnk (.conjL hL))) (.conjR hL))

theorem packet_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((HornRuleSyntax.matrix packetRule w r V env).iff (packetLocal w V r env)) := by
  apply Derives.conjI
  · exact .impI (packet_forward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))
  · exact .impI (packet_backward (ZFContext.add hZ _) w V r env (add hw _) (add hn _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureLocal
