import PPAC.Migration.Internal.PacketAffineInductionSyntax

/-! Internal row witnesses connect the induction predicate to actual recursive trace entries in both directions. -/
namespace PPAC.Migration.Internal.PacketAffineInductionEntry
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem entry_to_affine {m} {Γ : Context m} (wide : Bool) (w B V t d a : Fin m)
    (hI : Derives Γ (correct wide w B V t)) (he : Derives Γ (PacketHornAffineSyntax.entry wide w V d t a)) :
    Derives Γ (PacketAffineSyntax.affine w B d t a) := by
  let P := (PacketHornAffineSyntax.row wide w.castSucc d.castSucc t.castSucc a.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hI1 := of_eq (correct_rename wide w B V t Fin.castSucc) (under hI P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (PacketAffineSyntax.affine_rename w B d t a Fin.castSucc).symm
    (.impE (.conjL (at_correct wide w.castSucc B.castSucc V.castSucc t.castSucc d.castSucc a.castSucc (Fin.last m) hI1 (.conjL hP))) (.conjR hP))

theorem affine_to_entry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V t d a : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (correct wide w B V t))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d t a)) : Derives Γ (PacketHornAffineSyntax.entry wide w V d t a) := by
  have hd := PacketAffineCore.digit_natural hZ w B d t a hw ha
  have ht := PacketAffineCore.tail_guard w B d t a ha
  have hy := PacketAffineCore.output_guard w B d t a ha
  have hi : Derives Γ (SyntaxForestSyntax.inputs 3 w (SyntaxAtomSyntax.three d t a)) :=
    SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three d t a)
      (Fin.cases hd (Fin.cases ht (Fin.cases hy (fun i => Fin.elim0 i))))
  have he := SyntaxConstructors.exists_constructor hZ 3 (PacketAffineRuleData.relation wide) w (SyntaxAtomSyntax.three d t a) hw hi
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (PacketHornAffineSyntax.row wide w.castSucc d.castSucc t.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hI1 := of_eq (correct_rename wide w B V t Fin.castSucc) (under hI P)
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w B d t a Fin.castSucc) (under ha P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hm := Derives.impE (.conjR (at_correct wide w.castSucc B.castSucc V.castSucc t.castSucc d.castSucc a.castSucc (Fin.last m) hI1 (.conjR hP))) ha1
  exact of_eq (PacketHornAffineSyntax.entry_rename wide w V d t a Fin.castSucc).symm
    (PacketTraceCore.intro_entry wide w.castSucc V.castSucc d.castSucc t.castSucc a.castSucc (Fin.last m) (.conjR hP) hm)

end PPAC.Migration.Internal.PacketAffineInductionEntry
