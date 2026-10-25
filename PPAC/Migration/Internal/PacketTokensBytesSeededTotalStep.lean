import PPAC.Migration.Internal.PacketTokensBytesSeededTotalPoint

/-! Original strict membership of the actual Cons tail code discharges the all-tail seeded-fiber induction step. -/
namespace PPAC.Migration.Internal.PacketTokensBytesSeededTotalStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokensBytesSyntax PacketTokensBytesSeededTotalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) : Derives Γ (fiber w n t) := by
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w n hw hn)
  · exact PacketTokensBytesSeededTotalPoint.nil_fiber (ZFContext.add hZ _) _ _ _ (add hw _) (.hyp (Or.inl rfl)) (add ht _)
  · let P := StructuralListDecodeSyntax.tailCase w n
    let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) R
    have hx := StructuralListValidity.range _ _ (.conjL hR)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Ξ := Context.add H (Context.image Formula.raise Δ)
    apply Derives.exE (p := H) (.conjR hR)
    have hH : Derives Ξ H := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 H
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under (add hw P) R) H)
    have hi2 : Derives Ξ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,earlier_rename]) (under (under (add hi P) R) H)
    have ht2 : Derives Ξ (StructuralListTraceSyntax.valid w.castSucc.castSucc t.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListTraceSyntax.valid_rename]) (under (under (add ht P) R) H)
    have hxV := of_eq (StructuralListTraceSyntax.valid_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) H)
    have hxN : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hx H
    have hb := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) hxN (.conjR hH)
    have hp := earlier_at _ _ _ hi2 hxN (.conjR hb)
    have hSmall := at_tail _ _ _ hp hxV ht2
    simpa only [Formula.raise,fiber_rename] using PacketTokensBytesSeededTotalPoint.cons_fiber hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc t.castSucc.castSucc hw2 (.conjL hH) hxN (.conjR hH) hSmall

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.impI
  let N := StructuralListTraceSyntax.valid w n
  apply Derives.allI
  apply Derives.impI
  let T := StructuralListTraceSyntax.valid w.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise (Context.add N Γ))
  have hZ1 := ZFContext.under (ZFContext.add hZ N) T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) T)
  have hi1 := of_eq (earlier_rename w n Fin.castSucc) (under (add hi N) T)
  have hn1 := of_eq (StructuralListTraceSyntax.valid_rename w n Fin.castSucc) (under (.hyp (Or.inl rfl) : Derives (Context.add N Γ) N) T)
  exact from_earlier_point hZ1 w.castSucc n.castSucc (Fin.last m) hw1 hi1 hn1 (.hyp (Or.inl rfl) : Derives Δ T)

end PPAC.Migration.Internal.PacketTokensBytesSeededTotalStep
