import PPAC.Migration.Internal.PacketVarintDomain

/-! Actual sequence graphs construct terminal and nonzero continuation LEB128 prefixes; no Tok premise. -/
namespace PPAC.Migration.Internal.PacketVarintConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_not_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h s p : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (StructuralListSyntax.consCode w h s p)) :
    Derives Γ (StructuralListSyntax.nilCode w p).neg := by
  apply Derives.impI
  exact StructuralConsUnique.disjoint (ZFContext.add hZ _) w h s p (add hw _) (.hyp (Or.inl rfl)) (add hc _)

theorem terminal_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n e s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hn : Derives Γ (.mem n B))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) (hs : Derives Γ (StructuralListSyntax.consCode w n e s)) : Derives Γ (canonicalAt w B n s) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (SyntaxNumerals.exists_numeral hZ 0 w hw)
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he Z)
  have hs1 := of_eq (StructuralListSyntax.consCode_rename w n e s Fin.castSucc) (under hs Z)
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have hf := PacketVarintTraceBase.nil_fold hZ1 w.castSucc B.castSucc e.castSucc (Fin.last m) hw1 he1 (.conjL hZ0)
  have hcell := PacketVarintCell.terminal_cell hZ1 w.castSucc B.castSucc e.castSucc n.castSucc (Fin.last m) hw1 (under hB Z) he1 (.conjR hZ0) (under hn Z)
  have hout := PacketVarintTraceAppend.cons_fold hZ1 w.castSucc B.castSucc e.castSucc (Fin.last m) (Fin.last m) n.castSucc s.castSucc n.castSucc hw1 hf hs1 hcell
  simpa only [Formula.raise,canonicalAt_rename] using intro_at w.castSucc B.castSucc n.castSucc s.castSucc (Fin.last m) (.conjR hZ0) hout (cons_not_nil hZ1 w.castSucc n.castSucc e.castSucc s.castSucc hw1 hs1)

theorem continuation_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B q s d h n p : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (empty q).neg) (hf : Derives Γ (canonicalAt w B q s))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hsum : Derives Γ (NaturalAdditionSyntax.sum w d B h))
    (hp : Derives Γ (StructuralListSyntax.consCode w h s p)) : Derives Γ (canonicalAt w B n p) := by
  let Z := (empty (Fin.last m)).conj ((PacketVarintTraceSyntax.foldAt w.castSucc B.castSucc s.castSucc (Fin.last m) q.castSucc).conj
    (StructuralListSyntax.nilCode w.castSucc s.castSucc).neg)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) hf
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hq1 : Derives Δ (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq Z
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under ha Z)
  have hs1 := of_eq (NaturalAdditionSyntax.sum_rename w d B h Fin.castSucc) (under hsum Z)
  have hp1 := of_eq (StructuralListSyntax.consCode_rename w h s p Fin.castSucc) (under hp Z)
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have hcell := PacketVarintCell.continuation_cell hZ1 w.castSucc B.castSucc s.castSucc h.castSucc q.castSucc n.castSucc d.castSucc hw1 hq1 ha1 hs1
  have hout := PacketVarintTraceAppend.cons_fold hZ1 w.castSucc B.castSucc s.castSucc (Fin.last m) q.castSucc h.castSucc p.castSucc n.castSucc hw1 (.conjL (.conjR hZ0)) hp1 hcell
  simpa only [Formula.raise,canonicalAt_rename] using intro_at w.castSucc B.castSucc n.castSucc p.castSucc (Fin.last m) (.conjL hZ0) hout (cons_not_nil hZ1 w.castSucc h.castSucc s.castSucc p.castSucc hw1 hp1)

theorem terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n e s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n B))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) (hs : Derives Γ (StructuralListSyntax.consCode w n e s)) : Derives Γ (canonical w n s) :=
  intro_actual w B n s hB (terminal_at hZ w B n e s hw (SyntaxNumerals.range hZ 128 w B hw hB) hn he hs)

theorem continuation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B q s d h n p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hq : Derives Γ (empty q).neg)
    (hf : Derives Γ (canonical w q s)) (ha : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) (hp : Derives Γ (StructuralListSyntax.consCode w h s p)) : Derives Γ (canonical w n p) :=
  intro_actual w B n p hB (continuation_at hZ w B q s d h n p hw hq (PacketVarintDomain.at_radix hZ w B q s hB hf) ha hs hp)

end PPAC.Migration.Internal.PacketVarintConstruct
