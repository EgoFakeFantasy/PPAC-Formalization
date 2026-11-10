import PPAC.Migration.ForcingWeakenedImages
import PPAC.Migration.ForcingPreorderMember
import PPAC.Migration.Internal.SyntaxWeakenFreeAtoms

/-! Actual original member leaves under first-free0 freshening. The old
and new carrier fields are object witnesses. Original raw member readers,
push fields and weak atomic constructor law are reused, without matching
irrelevant fresh-r slots or assuming any desired member/weak answer. -/
namespace PPAC.Migration.ForcingMemberWeakening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def atomInput {m} (w z b B Ib Jb I J P V Pn Vn n N : Fin m) : Formula m :=
  (omega w).conj ((ForcingWeakenedImages.operations w z b B Ib Jb I J).conj
    ((SyntaxRenameTermSyntax.renamed w I J z b z B P Pn).conj
      ((SyntaxRenameTermSyntax.renamed w I J z b z B V Vn).conj
        ((ForcingMemberGuardOpening.result w P V n).conj (ForcingMemberGuardOpening.result w Pn Vn N)))))
private theorem atomInput_rename {m l} (w z b B Ib Jb I J P V Pn Vn n N : Fin m) (ρ : Fin m → Fin l) :
    (atomInput w z b B Ib Jb I J P V Pn Vn n N).rename ρ =
      atomInput (ρ w) (ρ z) (ρ b) (ρ B) (ρ Ib) (ρ Jb) (ρ I) (ρ J) (ρ P) (ρ V) (ρ Pn) (ρ Vn) (ρ n) (ρ N) := by
  simp only [atomInput, Formula.rename, omega_rename, ForcingWeakenedImages.operations_rename,
    SyntaxRenameTermSyntax.renamed_rename, ForcingMemberGuardOpening.result_rename]

private theorem at_atoms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b B Ib Jb I J P V Pn Vn n N : Fin m) (hi : Derives Γ (atomInput w z b B Ib Jb I J P V Pn Vn n N)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B n N) := by
  have hOld := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  let E := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) P.castSucc V.castSucc n.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hOld
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := of_eq (atomInput_rename w z b B Ib Jb I J P V Pn Vn n N Fin.castSucc) (under hi E)
  let H := (SyntaxAtomSyntax.zeroScalar (old 2 w) (slot 2 1)).conj
    (SyntaxAtomSyntax.memberCode (old 2 w) (slot 2 1) (old 2 Pn) (old 2 Vn) (old 2 N))
  let Ξ := Context.add H (Context.image Formula.raise Δ)
  apply Derives.exE (p := H) (.conjR (.conjR (.conjR (.conjR (.conjR h1)))))
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have h2 : Derives Ξ (atomInput (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 Ib) (old 2 Jb) (old 2 I) (old 2 J)
      (old 2 P) (old 2 V) (old 2 Pn) (old 2 Vn) (old 2 n) (old 2 N)) :=
    of_eq (by simp only [Formula.raise, atomInput_rename]; rfl) (under h1 H)
  have hOld2 : Derives Ξ ((SyntaxAtomSyntax.zeroScalar (old 2 w) (slot 2 0)).conj
      (SyntaxAtomSyntax.memberCode (old 2 w) (slot 2 0) (old 2 P) (old 2 V) (old 2 n))) :=
    of_eq (by simp only [E, Formula.raise, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename]; rfl) (under hE H)
  have hZ2 := ZFContext.under (ZFContext.under hZ E) H
  have hw := Derives.conjL h2
  have ho := Derives.conjL (.conjR h2)
  have hSym := SyntaxZeroScalar.unique hZ2 (old 2 w) (slot 2 0) (slot 2 1) hw (.conjL hOld2) (.conjL hH)
  have hAtom := SyntaxWeakenFreeAtoms.membership_iff hZ2 (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 n) (old 2 N)
    (old 2 Ib) (old 2 Jb) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 P) (old 2 V) (old 2 Pn) (old 2 Vn) hw (.conjL ho) (.conjL (.conjR ho))
    (.conjL (.conjR (.conjR ho))) (.conjR (.conjR (.conjR ho))) (.conjR hOld2) (.conjR hH)
  have out : Derives Ξ (SyntaxWeakenFreeSyntax.weakened (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 n) (old 2 N)) :=
    .impE (.conjR hAtom) (.conjI (.conjL hOld2) (.conjI hSym
    (.conjI (.conjL (.conjR (.conjR h2))) (.conjL (.conjR (.conjR (.conjR h2)))))))
  have eqRaise : (SyntaxWeakenFreeSyntax.weakened w z b B n N).raise.raise =
      SyntaxWeakenFreeSyntax.weakened (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 n) (old 2 N) := by
    simp only [Formula.raise, SyntaxWeakenFreeSyntax.weakened_rename]; rfl
  exact of_eq eqRaise.symm out

def reader {m} (w S K P n : Fin m) : Formula m := .all
  ((field w.castSucc S.castSucc K.castSucc (Fin.last m)).imp
    (ForcingMemberGuardOpening.result w.castSucc P.castSucc (Fin.last m) n.castSucc))
theorem reader_rename {m l} (w S K P n : Fin m) (ρ : Fin m → Fin l) :
    (reader w S K P n).rename ρ = reader (ρ w) (ρ S) (ρ K) (ρ P) (ρ n) := by
  simp only [reader, Formula.rename, field_rename, ForcingMemberGuardOpening.result_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem reader_at {m} {Γ : Context m} (w S K P n V : Fin m) (hr : Derives Γ (reader w S K P n))
    (hv : Derives Γ (field w S K V)) : Derives Γ (ForcingMemberGuardOpening.result w P V n) :=
  .impE (of_eq (by simp only [Formula.instantiate, Formula.rename, field_rename, ForcingMemberGuardOpening.result_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE V hr)) hv

def input {m} (w z f b B R S K P Pn n N : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (ForcingWeakenedImages.data w z f z b B R S v).conj ((Formula.mem K f).conj
    ((SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B P Pn).conj
      ((reader w S K P n).conj (reader w (v 9) K Pn N))))
theorem input_rename {m l} (w z f b B R S K P Pn n N : Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (input w z f b B R S K P Pn n N v).rename ρ =
      input (ρ w) (ρ z) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K) (ρ P) (ρ Pn) (ρ n) (ρ N) (fun i => ρ (v i)) := by
  simp only [input, Formula.rename, ForcingWeakenedImages.data_rename, reader_rename, SyntaxRenameTermSyntax.renamed_rename]

private def images {m} (v : Fin 10 → Fin m) : Fin 6 → Fin m :=
  Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases (v 6) (Fin.cases (v 7) (SyntaxAtomSyntax.two (v 8) (v 9)))))

private theorem at_carrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f b B R S K P Pn n N V : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (input w z f b B R S K P Pn n N v))
    (hV : Derives Γ (field w S K V)) : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B n N) := by
  have hBase := Derives.conjL hi
  have hw := Derives.conjL (.conjL hBase)
  have hLists := Derives.conjR (.conjR (.conjL hBase))
  have hf := Derives.conjL (.conjR hLists)
  have hk := StructuralListTraceOrder.member_member hZ w K f hw hf (.conjL (.conjR hi))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc (v 9).castSucc K.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (StructuralListFieldValues.exists_value hZ w (v 9) K hw hk)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := of_eq (input_rename w z f b B R S K P Pn n N v Fin.castSucc) (under hi E)
  have hZ1 := ZFContext.under hZ E
  have hB1 := Derives.conjL h1
  have hK1 := Derives.conjL (.conjR h1)
  have hOldV := of_eq (field_rename w S K V Fin.castSucc) (under hV E)
  have hVn := Derives.impE (.conjL (ForcingReindexedImages.field_iff hZ1 false
    w.castSucc z.castSucc f.castSucc z.castSucc b.castSucc z.castSucc B.castSucc R.castSucc S.castSucc (v 2).castSucc (v 3).castSucc
    K.castSucc V.castSucc (Fin.last m) (images (fun i => (v i).castSucc)) (.conjR (.conjR hB1)) (.conjI hK1 hOldV)))
    (.conjI hK1 (.conjR hE))
  have hOld := reader_at w.castSucc S.castSucc K.castSucc P.castSucc n.castSucc V.castSucc
    (.conjL (.conjR (.conjR (.conjR h1)))) hOldV
  have hNew := reader_at w.castSucc (v 9).castSucc K.castSucc Pn.castSucc N.castSucc (Fin.last m)
    (.conjR (.conjR (.conjR (.conjR h1)))) (.conjR hE)
  have hAtom : Derives Δ (atomInput w.castSucc z.castSucc b.castSucc B.castSucc
      (v 0).castSucc (v 1).castSucc (v 2).castSucc (v 3).castSucc P.castSucc V.castSucc Pn.castSucc (Fin.last m) n.castSucc N.castSucc) :=
    .conjI (.conjL (.conjL hB1)) (.conjI (.conjL (.conjR hB1))
      (.conjI (.conjL (.conjR (.conjR h1))) (.conjI hVn (.conjI hOld hNew))))
  have ho := at_atoms hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAtom
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w z b B n N Fin.castSucc).symm ho

/-- Both carrier fields and both member-symbol witnesses are internally
generated/eliminated. These readers will themselves be proved from the
actual original rows below; no carrier or raw-member answer is supplied. -/
theorem from_readers {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f b B R S K P Pn n N : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (input w z f b B R S K P Pn n N v)) : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B n N) := by
  have hBase := Derives.conjL hi
  have hw := Derives.conjL (.conjL hBase)
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjL hBase))))
  have hk := StructuralListTraceOrder.member_member hZ w K f hw hf (.conjL (.conjR hi))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc S.castSucc K.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (StructuralListFieldValues.exists_value hZ w S K hw hk)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_carrier (ZFContext.under hZ E) w.castSucc z.castSucc f.castSucc b.castSucc B.castSucc R.castSucc S.castSucc
    K.castSucc P.castSucc Pn.castSucc n.castSucc N.castSucc (Fin.last m) (fun i => (v i).castSucc)
    (of_eq (input_rename w z f b B R S K P Pn n N v Fin.castSucc) (under hi E)) (.conjR hE)
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w z b B n N Fin.castSucc).symm ho

private theorem reader_from_row {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C Bound S Refl Pre K : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m)
    (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hd : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f T C Bound S Refl Pre raw G H U F P N D)) :
    Derives Γ (reader w S K (P i) (H (ForcingPreorderMember.memberPosition i))) := by
  apply Derives.allI
  apply Derives.impI
  let E := field w.castSucc S.castSucc K.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact ForcingPreorderMember.raw_from_data (ZFContext.under hZ E) test Reln i
    w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc T.castSucc C.castSucc Bound.castSucc S.castSucc
    Refl.castSucc Pre.castSucc K.castSucc (Fin.last m) (fun x => (raw x).castSucc) (fun x => (G x).castSucc)
    (fun x => (H x).castSucc) (fun x => (U x).castSucc) (fun x => (F x).castSucc) (fun x => (P x).castSucc)
    (fun x => (N x).castSucc) (fun x => (D x).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw E))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E))
    (of_eq (SyntaxNumeralSyntax.numeral_rename k K Fin.castSucc) (under hK E))
    (of_eq (ForcingPreorderLeaves.data_rename test Reln w z A1 A2 A3 f T C Bound S Refl Pre raw G H U F P N D Fin.castSucc) (under hd E)) hE

/-- The two actual original rows share the raw source and pushed tables.
Only the selected condition term is compared; the fresh r slot may differ. -/
def rowsFrame {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre : Fin 2 → Fin m) (G : Fin 2 → Fin 5 → Fin m) (H : Fin 2 → Fin 6 → Fin m)
    (U F P : Fin 2 → Fin 3 → Fin m) (N : Fin 2 → Fin 5 → Fin m) (D : Fin 2 → Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral k K).conj
      ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((ForcingWeakenedImages.data w z f z b B R S v).conj
        ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) raw (G 0) (H 0) (U 0) (F 0) (P 0) (N 0) (D 0)).conj
          ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) raw (G 1) (H 1) (U 1) (F 1) (P 1) (N 1) (D 1)).conj
            (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B (P 0 i) (P 1 i)))))))))

theorem rowsFrame_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre : Fin 2 → Fin m) (G : Fin 2 → Fin 5 → Fin m) (H : Fin 2 → Fin 6 → Fin m)
    (U F P : Fin 2 → Fin 3 → Fin m) (N : Fin 2 → Fin 5 → Fin m) (D : Fin 2 → Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (rowsFrame test Reln i w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D).rename ρ =
      rowsFrame test Reln i (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) (fun s => ρ (C s)) (fun s => ρ (Refl s)) (fun s => ρ (Pre s))
        (fun s j => ρ (G s j)) (fun s j => ρ (H s j)) (fun s j => ρ (U s j)) (fun s j => ρ (F s j))
        (fun s j => ρ (P s j)) (fun s j => ρ (N s j)) (fun s j => ρ (D s j)) := by
  simp only [rowsFrame, Formula.rename, SyntaxNumeralSyntax.numeral_rename, ForcingWeakenedImages.data_rename,
    ForcingPreorderLeaves.data_rename, SyntaxRenameTermSyntax.renamed_rename]

/-- Read both original member outputs from actual native-instance rows,
produce their carrier fields, and derive the original weakening relation. -/
theorem from_rows {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre : Fin 2 → Fin m) (G : Fin 2 → Fin 5 → Fin m) (H : Fin 2 → Fin 6 → Fin m)
    (U F P : Fin 2 → Fin 3 → Fin m) (N : Fin 2 → Fin 5 → Fin m) (D : Fin 2 → Fin 3 → Fin m)
    (hi : Derives Γ (rowsFrame test Reln i w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B
      (H 0 (ForcingPreorderMember.memberPosition i)) (H 1 (ForcingPreorderMember.memberPosition i))) := by
  have h0 := Derives.conjL hi
  have h1 := Derives.conjL (.conjR hi)
  have h2 := Derives.conjL (.conjR (.conjR hi))
  have hK := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  have ht := Derives.conjR (.conjR (.conjR (.conjR (.conjR hi))))
  have hBase := Derives.conjL ht
  have hw := Derives.conjL (.conjL hBase)
  have hOld := reader_from_row hZ test Reln i w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) K
    raw (G 0) (H 0) (U 0) (F 0) (P 0) (N 0) (D 0) hw h0 h1 h2 hK (.conjL (.conjR ht))
  have hNew := reader_from_row hZ test Reln i w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) K
    raw (G 1) (H 1) (U 1) (F 1) (P 1) (N 1) (D 1) hw h0 h1 h2 hK (.conjL (.conjR (.conjR ht)))
  have hkf := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f K hf hK
  exact from_readers hZ w z f b B R S K (P 0 i) (P 1 i)
    (H 0 (ForcingPreorderMember.memberPosition i)) (H 1 (ForcingPreorderMember.memberPosition i)) v
    (.conjI hBase (.conjI hkf (.conjI (.conjR (.conjR (.conjR ht))) (.conjI hOld hNew))))

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre : Fin 2 → Fin m) (G : Fin 2 → Fin 5 → Fin m) (H : Fin 2 → Fin 6 → Fin m)
    (U F P : Fin 2 → Fin 3 → Fin m) (N : Fin 2 → Fin 5 → Fin m) (D : Fin 2 → Fin 3 → Fin m) : Source.Sentence :=
  ((rowsFrame test Reln i w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D).imp
    (SyntaxWeakenFreeSyntax.weakened w z b B
      (H 0 (ForcingPreorderMember.memberPosition i)) (H 1 (ForcingPreorderMember.memberPosition i)))).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre : Fin 2 → Fin m) (G : Fin 2 → Fin 5 → Fin m) (H : Fin 2 → Fin 6 → Fin m)
    (U F P : Fin 2 → Fin 3 → Fin m) (N : Fin 2 → Fin 5 → Fin m) (D : Fin 2 → Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln i w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_rows (ZFContext.add (ZFContext.source_ZF m) _) test Reln i w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D
    (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingMemberWeakening
