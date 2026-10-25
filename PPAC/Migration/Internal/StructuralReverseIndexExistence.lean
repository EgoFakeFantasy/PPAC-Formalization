import PPAC.Migration.Internal.StructuralReverseIndexArithmetic

/-! Every internal i<l has an actual reverse partner, obtained by the original predecessor and difference constructions. -/
namespace PPAC.Migration.Internal.StructuralReverseIndexExistence
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseIndexSyntax NaturalAdditionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l p i : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hi : Derives Γ (.mem i w))
    (hl : Derives Γ (successor l p)) (hI : Derives Γ (.mem i l)) : Derives Γ (existsMirror w l i) := by
  have hb := NaturalOrderBasic.member_successor i p l hl hI
  have hex := NaturalDifference.exists_of_below hZ w i p hw hi hp hb
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc i.castSucc (Fin.last m) p.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under hi R
  have hp1 : Derives Δ (.mem p.castSucc w.castSucc) := under hp R
  have hl1 := of_eq (successor_rename l p Fin.castSucc) (under hl R)
  have hm := intro_mirror w.castSucc l.castSucc i.castSucc (Fin.last m) p.castSucc hi1 (.conjL hR) (.conjI hp1 (.conjI (.conjR hR) hl1))
  simpa only [Formula.raise,existsMirror_rename] using intro_exists _ _ _ _ hm

theorem exists_partner {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hi : Derives Γ (.mem i l)) : Derives Γ (existsMirror w l i) := by
  have hiN := StructuralListTraceOrder.member_member hZ w i l hw hl hi
  have hsplit := OmegaStructureAlgebra.decomposition_at w l
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hl
  apply Derives.disjE hsplit
  · exact .botE (.impE (empty_at l i (.hyp (Or.inl rfl))) (add hi _))
  · let P := OmegaStructureSyntax.predecessor w l
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw P) R)
    have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under (add hiN P) R
    have hI1 : Derives Δ (.mem i.castSucc l.castSucc) := under (add hi P) R
    simpa only [Formula.raise,existsMirror_rename] using at_successor hZ1 _ _ _ _ hw1 (.conjL hR) hi1 (.conjR hR) hI1

end PPAC.Migration.Internal.StructuralReverseIndexExistence
