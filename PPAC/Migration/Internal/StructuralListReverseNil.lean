import PPAC.Migration.Internal.StructuralListReverseLaws

/-! The actual reverse graph has the exact original Nil case and normalizes every actual length witness. -/
namespace PPAC.Migration.Internal.StructuralListReverseNil
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListReverseSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListSyntax (nilCode nilCode_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem normalize_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l r : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hr : Derives Γ (reverses w n r)) : Derives Γ (atLength w n l r) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 := of_eq (hasLength_rename w n l Fin.castSucc) (under hl R)
  have he := StructuralListLengthUnique.unique hZ1 _ _ _ _ hw1 (.conjL (.conjR hR)) hl1
  simpa only [Formula.raise,atLength_rename] using length_subst _ _ _ _ _ he (.conjR hR)

theorem reading_empty {m} {Γ : Context m} (w n l r : Fin m) (hl : Derives Γ (empty l)) : Derives Γ (reading w n l r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  have hl2 := of_eq (empty_rename l (old 2)) (add (HornBinderRules.under_many 2 hl) H)
  exact .botE (.impE (empty_at (old 2 l) (slot 2 0) hl2) (.hyp (Or.inl rfl)))

theorem nil_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hr : Derives Γ (nilCode w r)) : Derives Γ (reverses w n r) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjL (.conjL hw))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hn1 := of_eq (nilCode_rename w n Fin.castSucc) (under hn R)
  have hr1 := of_eq (nilCode_rename w r Fin.castSucc) (under hr R)
  have hN := StructuralListLengthConstruct.nil_length hZ1 _ _ _ hw1 hn1 (.conjR hR)
  have hO := StructuralListLengthConstruct.nil_length hZ1 _ _ _ hw1 hr1 (.conjR hR)
  have hRead := reading_empty w.castSucc n.castSucc (Fin.last m) r.castSucc (.conjR hR)
  simpa only [Formula.raise,reverses_rename] using intro_reverse _ _ _ _ (.conjL hR) (.conjI hN (.conjI hO hRead))

theorem nil_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hr : Derives Γ (reverses w n r)) : Derives Γ (nilCode w r) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hn1 := of_eq (nilCode_rename w n Fin.castSucc) (under hn R)
  have hEmpty := StructuralListLengthRules.nil_empty hZ1 _ _ _ hw1 hn1 (.conjL (.conjR hR))
  simpa only [Formula.raise,nilCode_rename] using StructuralListLengthConstruct.nil_of_empty_length hZ1 _ _ _ (.conjL (.conjR (.conjR hR))) hEmpty

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) : Derives Γ ((reverses w n r).iff (nilCode w r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact nil_output (ZFContext.add hZ _) _ _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact nil_pair (ZFContext.add hZ _) _ _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListReverseNil
