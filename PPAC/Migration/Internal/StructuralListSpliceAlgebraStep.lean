import PPAC.Migration.Internal.StructuralListSpliceAlgebraPoint

/-! Actual original Cons tail-code membership discharges the genuine smaller-prefix algebra step. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSyntax StructuralListSpliceAlgebraSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) : Derives Γ ((rightNil w n).conj (associative w n)) := by
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w n hw hn)
  · have hp := StructuralListSpliceAlgebraPoint.nil_property (ZFContext.add hZ _) w n (add hw _) (.hyp (Or.inl rfl))
    exact .impE hp (add hn _)
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
    have hn2 : Derives Ξ (StructuralListTraceSyntax.valid w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListTraceSyntax.valid_rename]) (under (under (add hn P) R) H)
    have hxN : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hx H
    have hb := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) hxN (.conjR hH)
    have hSmall := earlier_at _ _ _ hi2 hxN (.conjR hb)
    have hProperty := StructuralListSpliceAlgebraPoint.cons_property hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc hw2 (.conjL hH) hxN (.conjR hH) hSmall
    simpa only [Formula.raise,Formula.rename,rightNil_rename,associative_rename] using Derives.impE hProperty hn2

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.impI
  exact from_earlier_point (ZFContext.add hZ _) _ _ (add hw _) (add hi _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListSpliceAlgebraStep
