import PPAC.Migration.Internal.ObjectPacketStructureTail

/-! Every original structural assignment is natural from its actual head and ordered premise rows, before any search bound is assumed. -/
namespace PPAC.Migration.Internal.PacketStructureSearchEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketStructureSyntax PacketStructureLocalSyntax PacketStructureApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem entry_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w V : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (entry k tag w V xs)) : Derives Γ (environmentNat k w xs) := by
  let P := (row k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) V.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename k w xs Fin.castSucc).symm
    (PacketStructureAcceptedForward.row_environment (ZFContext.under hZ P) k tag w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hw1 (.conjL hP))

theorem tree_at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r n : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (treeAt w V r n env)) : Derives Γ (environmentNat 7 w env) := by
  have hh := PacketStructureAcceptedForward.row_environment hZ 3 3 w r (SyntaxAtomSyntax.three n (env 2) (env 3)) hw (.conjL ha)
  have hf := entry_environment hZ 4 4 w V (four (env 1) (env 4) (env 2) (env 5)) hw (.conjL (.conjR ha))
  have ht := PacketTokenNatural.entry_environment hZ 2 w V (env 0) (env 6) (env 3) hw (.conjR (.conjR (.conjR ha)))
  have h0 := environmentNat_at w _ ht 0
  have h1 := environmentNat_at w _ hf 0
  have h2 := environmentNat_at w _ hh 1
  have h3 := environmentNat_at w _ hh 2
  have h4 := environmentNat_at w _ hf 1
  have h5 := environmentNat_at w _ hf 3
  have h6 := environmentNat_at w _ ht 1
  apply HornApplicationRules.intro_nat w env
  intro i
  exact Fin.cases h0 (fun j => Fin.cases h1 (fun k => Fin.cases h2 (fun l => Fin.cases h3
    (fun p => Fin.cases h4 (fun q => Fin.cases h5 (fun u => Fin.cases h6 (fun v => Fin.elim0 v) u) q) p) l) k) j) i

theorem nil_at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r z e : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (nilAt w r z e env)) : Derives Γ (environmentNat 1 w env) := by
  have hh := PacketStructureAcceptedForward.row_environment hZ 4 4 w r (four e z (env 0) (env 0)) hw ha
  apply HornApplicationRules.intro_nat w env
  intro i
  exact Fin.cases (environmentNat_at w _ hh 2) (fun j => Fin.elim0 j) i

theorem cons_at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r n s : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (consAt w V r n s env)) : Derives Γ (environmentNat 6 w env) := by
  have hh := PacketStructureAcceptedForward.row_environment hZ 4 4 w r (four n s (env 3) (env 4)) hw (.conjL ha)
  have hf := entry_environment hZ 4 4 w V (four (env 1) (env 2) (env 3) (env 5)) hw (.conjL (.conjR ha))
  have ht := entry_environment hZ 3 3 w V (SyntaxAtomSyntax.three (env 0) (env 5) (env 4)) hw (.conjR (.conjR ha))
  have h0 := environmentNat_at w _ ht 0
  have h1 := environmentNat_at w _ hf 0
  have h2 := environmentNat_at w _ hf 1
  have h3 := environmentNat_at w _ hh 2
  have h4 := environmentNat_at w _ hh 3
  have h5 := environmentNat_at w _ hf 3
  apply HornApplicationRules.intro_nat w env
  intro i
  exact Fin.cases h0 (fun j => Fin.cases h1 (fun k => Fin.cases h2 (fun l => Fin.cases h3
    (fun p => Fin.cases h4 (fun q => Fin.cases h5 (fun u => Fin.elim0 u) q) p) l) k) j) i

theorem packet_at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r e : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (packetAt w V r e env)) : Derives Γ (environmentNat 3 w env) := by
  have hh := PacketStructureAcceptedForward.row_environment hZ 2 5 w r (SyntaxAtomSyntax.two (env 1) (env 0)) hw (.conjL ha)
  have hp := PacketTokenNatural.entry_environment hZ 1 w V e (env 2) (env 1) hw (.conjL (.conjR ha))
  have h0 := environmentNat_at w _ hh 1
  have h1 := environmentNat_at w _ hh 0
  have h2 := environmentNat_at w _ hp 1
  apply HornApplicationRules.intro_nat w env
  intro i
  exact Fin.cases h0 (fun j => Fin.cases h1 (fun k => Fin.cases h2 (fun l => Fin.elim0 l) k) j) i

theorem tree_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (treeLocal w V r env)) : Derives Γ (environmentNat 7 w env) := by
  let L := PacketStructureLocalSyntax.treeBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename 7 w env (old 1)).symm
    (tree_at_natural (HornBinderRules.zf_body 1 hZ L) (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)) hwk (.conjR hL))

theorem nil_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (nilLocal w V r env)) : Derives Γ (environmentNat 1 w env) := by
  let L := PacketStructureLocalSyntax.nilBody w V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename 1 w env (old 2)).symm
    (nil_at_natural (HornBinderRules.zf_body 2 hZ L) (old 2 w) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) hwk (.conjR (.conjR hL)))

theorem cons_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (consLocal w V r env)) : Derives Γ (environmentNat 6 w env) := by
  let L := PacketStructureLocalSyntax.consBody w V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename 6 w env (old 2)).symm
    (cons_at_natural (HornBinderRules.zf_body 2 hZ L) (old 2 w) (old 2 V) (old 2 r) (slot 2 0) (slot 2 1) (fun i => old 2 (env i)) hwk (.conjR (.conjR hL)))

theorem packet_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (packetLocal w V r env)) : Derives Γ (environmentNat 3 w env) := by
  let L := PacketStructureLocalSyntax.packetBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename 3 w env (old 1)).symm
    (packet_at_natural (HornBinderRules.zf_body 1 hZ L) (old 1 w) (old 1 V) (old 1 r) (slot 1 0) (fun i => old 1 (env i)) hwk (.conjR hL))

theorem local_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (localCase b w V r env)) : Derives Γ (environmentNat (rule b).arity w env) := by
  cases b
  · exact tree_natural hZ w V r env hw hl
  · exact nil_natural hZ w V r env hw hl
  · exact cons_natural hZ w V r env hw hl
  · exact packet_natural hZ w V r env hw hl

end PPAC.Migration.Internal.PacketStructureSearchEnvironment
