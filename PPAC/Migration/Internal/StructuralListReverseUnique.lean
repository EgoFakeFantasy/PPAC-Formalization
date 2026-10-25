import PPAC.Migration.Internal.StructuralListReverseEncoding

/-! Original full-field list-code injectivity makes the actual reverse code unique, independent of all length and graph witnesses. -/
namespace PPAC.Migration.Internal.StructuralListReverseUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListReverseSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem agree_from_readings {m} {Γ : Context m} (w n l r s : Fin m)
    (hr : Derives Γ (reading w n l r)) (hs : Derives Γ (reading w n l s)) : Derives Γ (StructuralListCodeSyntax.agree w l r s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  have hr2 := of_eq (reading_rename w n l r (old 2)) (add (HornBinderRules.under_many 2 hr) H)
  have hs2 := of_eq (reading_rename w n l s (old 2)) (add (HornBinderRules.under_many 2 hs) H)
  have hR := reading_at (old 2 w) (old 2 n) (old 2 l) (old 2 r) (slot 2 0) (slot 2 1) hr2 (.hyp (Or.inl rfl))
  have hS := reading_at (old 2 w) (old 2 n) (old 2 l) (old 2 s) (slot 2 0) (slot 2 1) hs2 (.hyp (Or.inl rfl))
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjR hS) _) (.impE (add (.conjL hR) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hR) _) (.impE (add (.conjL hS) _) (.hyp (Or.inl rfl)))

theorem at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (atLength w n l r)) (hs : Derives Γ (atLength w n l s)) : Derives Γ (.equal r s) :=
  StructuralListCodeInduction.unique hZ w l r s hw (.conjL (.conjR hr)) (.conjL (.conjR hs))
    (agree_from_readings w n l r s (.conjR (.conjR hr)) (.conjR (.conjR hs)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (reverses w n r)) (hs : Derives Γ (reverses w n s)) : Derives Γ (.equal r s) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hs1 := of_eq (reverses_rename w n s Fin.castSucc) (under hs R)
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (atLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) s.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hs1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hR2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (atLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc)) :=
    of_eq (by simp only [R,Formula.raise,Formula.rename,atLength_rename]) (under hR T)
  have he := StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 (.conjL (.conjR hR2)) (.conjL (.conjR hT))
  have hc := length_subst _ _ _ _ _ he (.conjR hR2)
  exact at_length hZ2 _ _ _ _ _ hw2 hc (.conjR hT)

theorem valid_input {m} {Γ : Context m} (w n r : Fin m) (hr : Derives Γ (reverses w n r)) : Derives Γ (StructuralListTraceSyntax.valid w n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using StructuralListLengthBasic.valid_of_length _ _ _ (.conjL (.conjR hR))

theorem valid_output {m} {Γ : Context m} (w n r : Fin m) (hr : Derives Γ (reverses w n r)) : Derives Γ (StructuralListTraceSyntax.valid w r) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using StructuralListLengthBasic.valid_of_length _ _ _ (.conjL (.conjR (.conjR hR)))

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) : Derives Γ (fiber w n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (reverses w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListReverseEncoding.exists_reverse hZ w n hw hn)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all ((reverses w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := reverses w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    have hZ2 := ZFContext.under (ZFContext.under hZ R) T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
    have hOld := of_eq (reverses_rename w.castSucc n.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
    exact unique hZ2 _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Δ (fiber w.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,reverses_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hu)
  simpa only [Formula.raise,fiber_rename] using hout

end PPAC.Migration.Internal.StructuralListReverseUnique
