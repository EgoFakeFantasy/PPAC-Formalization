import PPAC.Migration.Internal.PacketVarintPrefixDomain

/-! Independent canonical prefixCode constructors use real original Nil/Cons and byte graphs; all code witnesses are eliminated. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintPrefixSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem terminal_at_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n t a e : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n B))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w n t a)) : Derives Γ (prefixCode w n t a) := by
  have hnN := PacketByteInputLaws.byte_natural hZ w n hw (.conjL (PacketBytesExecutionAffine.data hZ w n t a hw ha))
  have heN := StructuralNil.range hZ w e hw he
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc n.castSucc e.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralConsCore.exists_cons hZ w n e hw hnN heN)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he R)
  have ha1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w n t a Fin.castSucc) (under ha R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hc := PacketVarintConstruct.terminal hZ1 w.castSucc B.castSucc n.castSucc e.castSucc (Fin.last m) hw1 hB1 (under hn R) he1 (.conjR hR)
  have ht := Derives.conjL (Derives.conjR (PacketBytesExecutionAffine.data hZ1 w.castSucc n.castSucc t.castSucc a.castSucc hw1 ha1))
  have hb := PacketBytesLaws.singleton_bytes hZ1 w.castSucc e.castSucc (Fin.last m) t.castSucc n.castSucc a.castSucc hw1 he1 ht (.conjR hR) ha1
  simpa only [Formula.raise,prefixCode_rename] using intro_prefix w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m) hc hb

theorem terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hn : Derives Γ (.mem n B))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w n t a)) : Derives Γ (prefixCode w n t a) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using OrderedPairElimination.under_two hw U
  have hB2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using OrderedPairElimination.under_two hB U
  have ha2 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise,PacketAffineAcceptedSyntax.accepted_rename] using OrderedPairElimination.under_two ha U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have he := StructuralNil.at_unit hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hU) (.conjR hU)
  simpa only [Formula.raise,prefixCode_rename] using terminal_at_nil hZ2 w.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)) hw2 hB2 (OrderedPairElimination.under_two hn U) he ha2

theorem continuation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B q t u d h n a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hq : Derives Γ (empty q).neg)
    (hf : Derives Γ (prefixCode w q t u)) (hn : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (prefixCode w n t a) := by
  let R := body w q t u
  let ΓR := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hq1 : Derives ΓR (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq R
  have hn1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under hn R)
  have hs1 := of_eq (NaturalAdditionSyntax.sum_rename w d B h Fin.castSucc) (under hs R)
  have ha1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w h u a Fin.castSucc) (under ha R)
  have hR : Derives ΓR R := .hyp (Or.inl rfl)
  have hd := PacketVarintDomain.domain w.castSucc q.castSucc (Fin.last m) (.conjL hR)
  have hsN := StructuralListValidity.range _ _ (.conjL (.conjR hd))
  have hcell := PacketVarintCell.continuation_cell hZ1 w.castSucc B.castSucc (Fin.last m) h.castSucc q.castSucc n.castSucc d.castSucc hw1 hq1 hn1 hs1
  let P := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add P (Context.image Formula.raise ΓR)
  apply Derives.exE (p := P) (StructuralConsCore.exists_cons hZ1 w.castSucc h.castSucc (Fin.last m) hw1 (PacketVarintCell.head_natural _ _ _ _ _ _ hcell) hsN)
  have hZ2 := ZFContext.under hZ1 P
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 P)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B.castSucc Fin.castSucc) (under hB1 P)
  have hq2 : Derives Δ (empty q.castSucc.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq1 P
  have hn2 := of_eq (PacketAffineSyntax.affine_rename w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc Fin.castSucc) (under hn1 P)
  have hs2 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc d.castSucc B.castSucc h.castSucc Fin.castSucc) (under hs1 P)
  have ha2 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w.castSucc h.castSucc u.castSucc a.castSucc Fin.castSucc) (under ha1 P)
  have hc2 := of_eq (PacketVarintSyntax.canonical_rename w.castSucc q.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) P)
  have hb2 := of_eq (PacketBytesTraceSyntax.bytes_rename w.castSucc (Fin.last m) t.castSucc u.castSucc Fin.castSucc) (under (.conjR hR) P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hc := PacketVarintConstruct.continuation hZ2 w.castSucc.castSucc B.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc d.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) hw2 hB2 hq2 hc2 hn2 hs2 (.conjR hP)
  have hb := PacketBytesLaws.cons_bytes hZ2 w.castSucc.castSucc (Fin.last m).castSucc t.castSucc.castSucc u.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc hw2 hb2 (.conjR hP) ha2
  simpa only [Formula.raise,prefixCode_rename] using intro_prefix w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)) hc hb

end PPAC.Migration.Internal.PacketVarintPrefixConstruct
