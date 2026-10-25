import PPAC.Migration.Internal.StructuralListSpliceSnocSyntax
import PPAC.Migration.Internal.StructuralListSpliceSnocPoint

/-! Actual Cons recursion and the genuine smaller-prefix property preserve the full Snoc contract. -/
namespace PPAC.Migration.Internal.StructuralListSpliceSnocStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSnocSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b t n h S r l L : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (ht : Derives Γ (.mem t w))
    (hCons : Derives Γ (StructuralListSyntax.consCode w b t n)) (hi : Derives Γ (property w t))
    (hh : Derives Γ (.mem h w)) (hn : Derives Γ (StructuralListLengthSyntax.hasLength w n l))
    (hS : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w h S))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w n S r)) (hL : Derives Γ (successor L l)) :
    Derives Γ (StructuralListReverseConsContract.snoc w n l L h r) := by
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))).conj (StructuralListLengthSyntax.hasLength w.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (StructuralListLengthRules.cons_predecessor hZ w b t n l hw hb ht hCons hn)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w b t n Fin.castSucc) (under hCons P)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w n S r Fin.castSucc) (under hSp P)
  have hRem := StructuralListSplice.cons_forward hZ1 w.castSucc b.castSucc t.castSucc n.castSucc S.castSucc r.castSucc hw1 (under hb P) (under ht P) hc1 hSp1
  let Q := (StructuralListSpliceSyntax.splice w.castSucc.castSucc t.castSucc.castSucc S.castSucc.castSucc (Fin.last (m+1))).conj
    (StructuralListSyntax.consCode w.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc)
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hRem
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under hp P) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have hc2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc b.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hCons
  have hi2 : Derives Ξ (property w.castSucc.castSucc t.castSucc.castSucc) := by simpa only [Formula.raise,property_rename] using lift hi
  have hn2 : Derives Ξ (StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListLengthSyntax.hasLength_rename] using lift hn
  have hS2 : Derives Ξ (PacketVarintCanonicalRecursionSyntax.singleton w.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc) := by simpa only [Formula.raise,PacketVarintCanonicalRecursionSyntax.singleton_rename] using lift hS
  have hL2 : Derives Ξ (successor L.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise,successor_rename] using lift hL
  have hP2 : Derives Ξ (((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (successor l.castSucc.castSucc (Fin.last m).castSucc)).conj (StructuralListLengthSyntax.hasLength w.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [P,Formula.raise,Formula.rename,successor_rename,StructuralListLengthSyntax.hasLength_rename] using under hP Q
  have hCase := at_fields w.castSucc.castSucc t.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc l.castSucc.castSucc hi2
  have hTail := Derives.impE (Derives.impE (Derives.impE (Derives.impE (Derives.impE hCase (lift hh)) (.conjR hP2)) hS2) (.conjL hQ)) (.conjR (.conjL hP2))
  have hout := StructuralListSpliceSnocPoint.cons_shift hZ2 w.castSucc.castSucc b.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc L.castSucc.castSucc h.castSucc.castSucc
    hw2 (lift hb) hc2 (.conjR hQ) hn2 hL2 hTail
  simpa only [Formula.raise,StructuralListReverseConsContract.snoc_rename] using hout

theorem from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h S r l L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hh : Derives Γ (.mem h w))
    (hn : Derives Γ (StructuralListLengthSyntax.hasLength w n l)) (hS : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w h S))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w n S r)) (hL : Derives Γ (successor L l)) :
    Derives Γ (StructuralListReverseConsContract.snoc w n l L h r) := by
  have hValid := StructuralListLengthBasic.valid_of_length w n l hn
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w n hw hValid)
  · exact StructuralListSpliceSnocPoint.nil_point (ZFContext.add hZ _) w n l h S r L (add hw _) (.hyp (Or.inl rfl)) (add hn _) (add hh _) (add hS _) (add hSp _) (add hL _)
  · let A := StructuralListDecodeSyntax.tailCase w n
    let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add A Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ A) R
    have htN := StructuralListValidity.range _ _ (.conjL hR)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Ξ := Context.add H (Context.image Formula.raise Δ)
    apply Derives.exE (p := H) (.conjR hR)
    have hH : Derives Ξ H := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 H
    have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under (add hp A) R) H
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
    have hi2 : Derives Ξ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise,earlier_rename] using lift hi
    have hn2 : Derives Ξ (StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListLengthSyntax.hasLength_rename] using lift hn
    have hS2 : Derives Ξ (PacketVarintCanonicalRecursionSyntax.singleton w.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc) := by simpa only [Formula.raise,PacketVarintCanonicalRecursionSyntax.singleton_rename] using lift hS
    have hSp2 : Derives Ξ (StructuralListSpliceSyntax.splice w.castSucc.castSucc n.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSpliceSyntax.splice_rename] using lift hSp
    have hL2 : Derives Ξ (successor L.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise,successor_rename] using lift hL
    have ht2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under htN H
    have hBelow := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) ht2 (.conjR hH)
    have hSmall := earlier_at _ _ _ hi2 ht2 (.conjR hBelow)
    simpa only [Formula.raise,StructuralListReverseConsContract.snoc_rename] using cons_point hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc l.castSucc.castSucc L.castSucc.castSucc
      hw2 (.conjL hH) ht2 (.conjR hH) hSmall (lift hh) hn2 hS2 hSp2 hL2

end PPAC.Migration.Internal.StructuralListSpliceSnocStep
