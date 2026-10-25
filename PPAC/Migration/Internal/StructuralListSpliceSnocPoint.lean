import PPAC.Migration.Internal.ObjectPacketReaderVarintSegment

/-! Actual singleton splice gives the Nil snoc case; original Cons fields shift the exact snoc contract at every internal prefix index. -/
namespace PPAC.Migration.Internal.StructuralListSpliceSnocPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open StructuralListSyntax (nilCode nilCode_rename consCode consCode_rename)
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldSyntax (field field_rename)
open StructuralListCodeSyntax (agree agree_rename agree_at)
open StructuralListReverseConsContract (snoc snoc_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem empty_agree {m} {Γ : Context m} (w l a b : Fin m) (hl : Derives Γ (empty l)) : Derives Γ (agree w l a b) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  have hl2 := of_eq (empty_rename l (old 2)) (add (HornBinderRules.under_many 2 hl) H)
  exact .botE (.impE (empty_at (old 2 l) (slot 2 0) hl2) (.hyp (Or.inl rfl)))

theorem prefix_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b t n U r p l h i y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hN : Derives Γ (consCode w b t n)) (hR : Derives Γ (consCode w b U r))
    (hS : Derives Γ (snoc w t p l h U)) (hi : Derives Γ (.mem i l)) :
    Derives Γ ((field w r i y).iff (field w n i y)) := by
  have hlN := StructuralListLengthBasic.length_member w U l (.conjL (.conjR hS))
  have htN := StructuralListLengthBasic.code_member w t p (.conjL hS)
  have hUN := StructuralListLengthBasic.code_member w U l (.conjL (.conjR hS))
  have hiN := StructuralListTraceOrder.member_member hZ w i l hw hlN hi
  have hSplit := OmegaStructureAlgebra.decomposition_at w i (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiN
  apply Derives.disjE hSplit
  · let H := empty i
    have hZ0 := ZFContext.add hZ H
    have hZero : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hA := StructuralListFieldCons.zero_iff hZ0 w b U r i y (add hw H) (add hb H) (add hUN H) (add hR H) hZero
    have hB := StructuralListFieldCons.zero_iff hZ0 w b t n i y (add hw H) (add hb H) (add htN H) (add hN H) hZero
    exact StructuralListSuffixArithmetic.iff_trans hA (.conjI (.conjR hB) (.conjL hB))
  · let H := OmegaStructureSyntax.predecessor w i
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := P) (.hyp (Or.inl rfl))
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) P)
    have hN1 := of_eq (consCode_rename w b t n Fin.castSucc) (under (add hN H) P)
    have hR1 := of_eq (consCode_rename w b U r Fin.castSucc) (under (add hR H) P)
    have hS1 := of_eq (snoc_rename w t p l h U Fin.castSucc) (under (add hS H) P)
    have hpN := StructuralListLengthBasic.length_member _ _ _ (.conjL hS1)
    have hjP := SyntaxIndexLiftOrder.predecessor_member hZ1 w.castSucc p.castSucc l.castSucc i.castSucc (Fin.last m) hw1 hpN (.conjL (.conjR (.conjR hS1))) (under (add hi H) P) (.conjR hP)
    have hA := StructuralListFieldCons.successor_iff hZ1 w.castSucc b.castSucc U.castSucc r.castSucc (Fin.last m) i.castSucc y.castSucc hw1 (under (add hb H) P) (under (add hUN H) P) (.conjL hP) (.conjR hP) hR1
    have hB := StructuralListFieldCons.successor_iff hZ1 w.castSucc b.castSucc t.castSucc n.castSucc (Fin.last m) i.castSucc y.castSucc hw1 (under (add hb H) P) (under (add htN H) P) (.conjL hP) (.conjR hP) hN1
    have hAB := agree_at w.castSucc p.castSucc U.castSucc t.castSucc (Fin.last m) y.castSucc (.conjL (.conjR (.conjR (.conjR hS1)))) hjP
    simpa only [Formula.raise,Formula.rename,Formula.iff,field_rename] using
      StructuralListSuffixArithmetic.iff_trans (StructuralListSuffixArithmetic.iff_trans hA hAB) (.conjI (.conjR hB) (.conjL hB))

theorem prefix_agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b t n U r p l h : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hN : Derives Γ (consCode w b t n)) (hR : Derives Γ (consCode w b U r))
    (hS : Derives Γ (snoc w t p l h U)) : Derives Γ (agree w l r n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  let Δ := Context.add H (raisedContext 2 Γ)
  have lift2 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 2)) := add (HornBinderRules.under_many 2 hh) H
  have hZ2 := ZFContext.add (HornBinderRules.zf_many 2 hZ) H
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hN2 := of_eq (consCode_rename w b t n (old 2)) (lift2 hN)
  have hR2 := of_eq (consCode_rename w b U r (old 2)) (lift2 hR)
  have hS2 := of_eq (snoc_rename w t p l h U (old 2)) (lift2 hS)
  exact prefix_point hZ2 (old 2 w) (old 2 b) (old 2 t) (old 2 n) (old 2 U) (old 2 r) (old 2 p) (old 2 l) (old 2 h) (slot 2 0) (slot 2 1) hw2 (lift2 hb) hN2 hR2 hS2 (.hyp (Or.inl rfl))

theorem cons_shift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b t n U r p l L h : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hN : Derives Γ (consCode w b t n)) (hR : Derives Γ (consCode w b U r))
    (hn : Derives Γ (hasLength w n l)) (hL : Derives Γ (successor L l))
    (hS : Derives Γ (snoc w t p l h U)) : Derives Γ (snoc w n l L h r) := by
  have hUL := Derives.conjL (.conjR hS)
  have hUN := StructuralListLengthBasic.code_member w U l hUL
  have hpN := StructuralListLengthBasic.length_member w t p (.conjL hS)
  have hr := StructuralListLengthConstruct.cons_length hZ w b U r l L hw hb hR hUL hL
  have hAgree := prefix_agree hZ w b t n U r p l h hw hb hN hR hS
  have hLast := StructuralListFieldCons.successor_backward hZ w b U r p l h hw hb hUN hpN (.conjL (.conjR (.conjR hS))) hR (.conjR (.conjR (.conjR (.conjR hS))))
  exact .conjI hn (.conjI hr (.conjI hL (.conjI hAgree hLast)))

theorem nil_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l h S r L : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hl : Derives Γ (hasLength w n l))
    (hh : Derives Γ (.mem h w)) (hS : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w h S))
    (hSplice : Derives Γ (StructuralListSpliceSyntax.splice w n S r)) (hL : Derives Γ (successor L l)) :
    Derives Γ (snoc w n l L h r) := by
  have hlEmpty := StructuralListLengthRules.nil_empty hZ w n l hw hn hl
  have hEq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff hZ w n S r hw hn)) hSplice)
  let P := (nilCode w.castSucc (Fin.last m)).conj (consCode w.castSucc h.castSucc (Fin.last m) S.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hS
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hl1 := of_eq (hasLength_rename w n l Fin.castSucc) (under hl P)
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL P)
  have he1 := of_eq (empty_rename l Fin.castSucc) (under hlEmpty P)
  have hEq1 : Derives Δ (.equal S.castSucc r.castSucc) := under hEq P
  have hTailLength := StructuralListLengthConstruct.nil_length hZ1 w.castSucc (Fin.last m) l.castSucc hw1 (.conjL hP) he1
  have hLength := StructuralListLengthConstruct.cons_length hZ1 w.castSucc h.castSucc (Fin.last m) S.castSucc l.castSucc L.castSucc hw1 (under hh P) (.conjR hP) hTailLength hL1
  have hTailN := StructuralNil.range hZ1 _ _ hw1 (.conjL hP)
  have hLast := StructuralListFieldCons.zero_value hZ1 w.castSucc h.castSucc (Fin.last m) S.castSucc l.castSucc hw1 (under hh P) hTailN (.conjR hP) he1
  have hAgree := empty_agree w.castSucc l.castSucc S.castSucc n.castSucc he1
  have hSnoc : Derives Δ (snoc w.castSucc n.castSucc l.castSucc L.castSucc h.castSucc S.castSucc) := .conjI hl1 (.conjI hLength (.conjI hL1 (.conjI hAgree hLast)))
  let Q := snoc w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc L.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))
  have h0 : Q.instantiate S.castSucc = snoc w.castSucc n.castSucc l.castSucc L.castSucc h.castSucc S.castSucc := by
    simp only [Q,Formula.instantiate,snoc_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : Q.instantiate r.castSucc = snoc w.castSucc n.castSucc l.castSucc L.castSucc h.castSucc r.castSucc := by
    simp only [Q,Formula.instantiate,snoc_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  simpa only [Formula.raise,snoc_rename] using of_eq h1 (Derives.eqSubst Q hEq1 (of_eq h0.symm hSnoc))

end PPAC.Migration.Internal.StructuralListSpliceSnocPoint
