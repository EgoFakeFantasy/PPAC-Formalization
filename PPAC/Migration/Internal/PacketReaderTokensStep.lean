import PPAC.Migration.Internal.PacketReaderTokensPoint

/-! Strict membership of the actual Cons tail code supplies the genuine smaller-token-list property, then one fixed universally quantified formula is closed. -/
namespace PPAC.Migration.Internal.PacketReaderTokensStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderTokensSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n bytes A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o n)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n))
    (ha : Derives Γ (StructuralListTraceSyntax.valid w A)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes))
    (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) : Derives Γ (agreement w B z o bytes A O p) := by
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w n hw hn)
  · exact PacketReaderTokensPoint.nil_point (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl)) (add ha _) (add he _) (add hOut _)
  · let P := StructuralListDecodeSyntax.tailCase w n
    let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) R
    have htN := StructuralListValidity.range _ _ (.conjL hR)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Ξ := Context.add H (Context.image Formula.raise Δ)
    apply Derives.exE (p := H) (.conjR hR)
    have hH : Derives Ξ H := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 H
    have lift2 {φ : Formula m} (hh : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under (add hh P) R) H
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift2 hw
    have hB2 : Derives Ξ (SyntaxNumeralSyntax.numeral 128 B.castSucc.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using lift2 hB
    have hz2 : Derives Ξ (empty z.castSucc.castSucc) := by simpa only [Formula.raise,empty_rename] using lift2 hz
    have ho2 : Derives Ξ (successor o.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise,successor_rename] using lift2 ho
    have hi2 : Derives Ξ (earlier w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise,earlier_rename] using lift2 hi
    have ha2 : Derives Ξ (StructuralListTraceSyntax.valid w.castSucc.castSucc A.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using lift2 ha
    have he2 : Derives Ξ (PacketTokensBytes.encoded w.castSucc.castSucc n.castSucc.castSucc bytes.castSucc.castSucc) := by simpa only [Formula.raise,PacketTokensBytes.encoded_rename] using lift2 he
    have hOut2 : Derives Ξ (PacketReaderOutputOrder.output w.castSucc.castSucc A.castSucc.castSucc n.castSucc.castSucc O.castSucc.castSucc) := by simpa only [Formula.raise,PacketReaderOutputOrder.output_rename] using lift2 hOut
    have htV := of_eq (StructuralListTraceSyntax.valid_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) H)
    have htN2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under htN H
    have hBelow := Derives.conjR (StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) htN2 (.conjR hH))
    have hIH := earlier_at w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hi2 htN2 hBelow
    simpa only [Formula.raise,agreement_rename] using PacketReaderTokensPoint.cons_point hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc bytes.castSucc.castSucc A.castSucc.castSucc O.castSucc.castSucc p.castSucc.castSucc hw2 hB2 hz2 ho2 (.conjL hH) htV (.conjR hH) ha2 hIH he2 hOut2

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o n)) : Derives Γ (property w B z o n) := by
  apply Derives.impI
  let N := StructuralListTraceSyntax.valid w n
  apply OriginalUniversalBlock.intro_many 4 (body w B z o n)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let A := StructuralListTraceSyntax.valid (old 4 w) (slot 4 1)
  let E := PacketTokensBytes.encoded (old 4 w) (old 4 n) (slot 4 0)
  let O := PacketReaderOutputOrder.output (old 4 w) (slot 4 1) (old 4 n) (slot 4 2)
  let Δ := Context.add O (Context.add E (Context.add A (raisedContext 4 (Context.add N Γ))))
  have hZ4 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 4 (ZFContext.add hZ N)) A) E) O
  have lift4 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 4)) := add (add (add (HornBinderRules.under_many 4 (add hh N)) A) E) O
  have hw4 := of_eq (omega_rename w (old 4)) (lift4 hw)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (lift4 hB)
  have hz4 := of_eq (empty_rename z (old 4)) (lift4 hz)
  have ho4 := of_eq (successor_rename o z (old 4)) (lift4 ho)
  have hi4 := of_eq (earlier_rename w B z o n (old 4)) (lift4 hi)
  have hn4 : Derives Δ (StructuralListTraceSyntax.valid (old 4 w) (old 4 n)) :=
    of_eq (StructuralListTraceSyntax.valid_rename w n (old 4)) (add (add (add (HornBinderRules.under_many 4 (.hyp (Or.inl rfl) : Derives (Context.add N Γ) N)) A) E) O)
  have hA : Derives Δ A := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hE : Derives Δ E := .hyp (Or.inr (Or.inl rfl))
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  exact from_earlier_point hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hB4 hz4 ho4 hi4 hn4 hA hE hO

end PPAC.Migration.Internal.PacketReaderTokensStep
