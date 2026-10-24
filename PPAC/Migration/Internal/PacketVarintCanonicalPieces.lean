import PPAC.Migration.Internal.PacketVarintCanonicalRecursionSyntax

/-! Original equality transports the terminal head; nonzero value proves the actual restricted suffix is nonempty. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalPieces
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax PacketVarintCanonicalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_head {m} {Γ : Context m} (w h x s n : Fin m) (he : Derives Γ (.equal h n))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) : Derives Γ (StructuralListSyntax.consCode w n x s) := by
  let P := StructuralListSyntax.consCode w.castSucc (Fin.last m) x.castSucc s.castSucc
  have h0 : P.instantiate h = StructuralListSyntax.consCode w h x s := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate n = StructuralListSyntax.consCode w n x s := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem nonempty_suffix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B x z q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (PacketVarintTraceSyntax.foldAt w B x z q))
    (hq : Derives Γ (empty q).neg) : Derives Γ (StructuralListSyntax.nilCode w x).neg := by
  apply Derives.impI
  have he := PacketVarintTraceBase.nil_value (ZFContext.add hZ _) w B x z q (add hw _) (.hyp (Or.inl rfl)) (add hf _)
  exact .impE (add hq _) (NaturalMultiplicationLaws.empty_subst z q he (add hz _))

theorem terminal_point {m} {Γ : Context m} (w B s n h x q : Fin m)
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (ht : Derives Γ (PacketVarintCellSyntax.terminal w B x h q n)) :
    Derives Γ (smallCase w B n s) := by
  have he := eq_symm (.conjR (.conjR (.conjR ht)))
  exact .conjI (mem_subst he (.conjL (.conjR (.conjR ht))))
    (intro_singleton w n s x (.conjL ht) (cons_head w h x s n he hc))

end PPAC.Migration.Internal.PacketVarintCanonicalPieces
