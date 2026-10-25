import PPAC.Migration.Internal.StructuralListReverseCons

/-! The actual Cons reversal equation uses a uniquely specified original snoc code, with every prefix field and final head fixed. -/
namespace PPAC.Migration.Internal.StructuralListReverseConsContract
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListReverseSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldSyntax (field field_rename)
open StructuralListSyntax (consCode consCode_rename)
open StructuralListCodeSyntax (agree agree_rename agree_at)
open SyntaxRenameQuerySyntax (of_eq)

def snoc {m} (w u l L h r : Fin m) : Formula m :=
  (hasLength w u l).conj ((hasLength w r L).conj ((successor L l).conj ((agree w l r u).conj (field w r l h))))

theorem snoc_rename {m k} (w u l L h r : Fin m) (ρ : Fin m → Fin k) :
    (snoc w u l L h r).rename ρ = snoc (ρ w) (ρ u) (ρ l) (ρ L) (ρ h) (ρ r) := by
  simp only [snoc,Formula.rename,hasLength_rename,successor_rename,agree_rename,field_rename]

theorem prefix_agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hl : Derives Γ (.mem l w))
    (hL : Derives Γ (successor L l)) (hc : Derives Γ (consCode w h t n))
    (hu : Derives Γ (reading w t l u)) (hr : Derives Γ (reading w n L r)) : Derives Γ (agree w l r u) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  let Δ := Context.add H (raisedContext 2 Γ)
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := add (HornBinderRules.under_many 2 hp) H
  have hZ2 := ZFContext.add (HornBinderRules.zf_many 2 hZ) H
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hh2 : Derives Δ (.mem (old 2 h) (old 2 w)) := lift2 hh
  have ht2 : Derives Δ (.mem (old 2 t) (old 2 w)) := lift2 ht
  have hl2 : Derives Δ (.mem (old 2 l) (old 2 w)) := lift2 hl
  have hL2 := of_eq (successor_rename L l (old 2)) (lift2 hL)
  have hc2 := of_eq (consCode_rename w h t n (old 2)) (lift2 hc)
  have hu2 := of_eq (reading_rename w t l u (old 2)) (lift2 hu)
  have hr2 := of_eq (reading_rename w n L r (old 2)) (lift2 hr)
  exact StructuralListReverseCons.prefix_at hZ2 (old 2 w) (old 2 h) (old 2 t) (old 2 n) (old 2 l) (old 2 L) (old 2 u) (old 2 r) (slot 2 0) (slot 2 1) hw2 hh2 ht2 hl2 hL2 hc2 hu2 hr2 (.hyp (Or.inl rfl))

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (consCode w h t n))
    (ht : Derives Γ (hasLength w t l)) (hL : Derives Γ (successor L l))
    (hu : Derives Γ (reverses w t u)) (hr : Derives Γ (reverses w n r)) : Derives Γ (snoc w u l L h r) := by
  have htN := StructuralListLengthBasic.code_member w t l ht
  have hlN := StructuralListLengthBasic.length_member w t l ht
  have hN := StructuralListLengthConstruct.cons_length hZ w h t n l L hw hh hc ht hL
  have hU := StructuralListReverseNil.normalize_length hZ w t l u hw ht hu
  have hR := StructuralListReverseNil.normalize_length hZ w n L r hw hN hr
  have hPrefix := prefix_agree hZ w h t n l L u r hw hh htN hlN hL hc (.conjR (.conjR hU)) (.conjR (.conjR hR))
  have hLast := StructuralListReverseCons.last_iff hZ w h t n l L r h hw hh htN hlN hL hc (.conjR (.conjR hR))
  exact .conjI (.conjL (.conjR hU)) (.conjI (.conjL (.conjR hR)) (.conjI hL (.conjI hPrefix (.impE (.conjR hLast) (.eqRefl h)))))

theorem last_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s i h y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hr : Derives Γ (field w r i h)) (hs : Derives Γ (field w s i h)) : Derives Γ ((field w r i y).iff (field w s i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    have he := StructuralListFieldValues.unique (ZFContext.add hZ _) w r i y h (add hw _) (add hi _) (.hyp (Or.inl rfl)) (add hr _)
    exact StructuralListFieldSyntax.output_subst _ _ _ _ _ (eq_symm he) (add hs _)
  · apply Derives.impI
    have he := StructuralListFieldValues.unique (ZFContext.add hZ _) w s i y h (add hw _) (add hi _) (.hyp (Or.inl rfl)) (add hs _)
    exact StructuralListFieldSyntax.output_subst _ _ _ _ _ (eq_symm he) (add hr _)

theorem snoc_agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w u l L h r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (snoc w u l L h r)) (hs : Derives Γ (snoc w u l L h s)) : Derives Γ (agree w L r s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 L)
  let Δ := Context.add H (raisedContext 2 Γ)
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := add (HornBinderRules.under_many 2 hp) H
  have hZ2 := ZFContext.add (HornBinderRules.zf_many 2 hZ) H
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hr2 := of_eq (snoc_rename w u l L h r (old 2)) (lift2 hr)
  have hs2 := of_eq (snoc_rename w u l L h s (old 2)) (lift2 hs)
  have hLN := StructuralListLengthBasic.length_member _ _ _ (.conjL (.conjR hr2))
  have hiN := StructuralListTraceOrder.member_member hZ2 (old 2 w) (slot 2 0) (old 2 L) hw2 hLN (.hyp (Or.inl rfl))
  have hCases := InsertLogic.member_cases (old 2 L) (old 2 l) (old 2 l) (slot 2 0) (.conjL (.conjR (.conjR hr2))) (.hyp (Or.inl rfl))
  apply Derives.disjE hCases
  · let I := Formula.mem (slot 2 0) (old 2 l)
    have hR := agree_at (old 2 w) (old 2 l) (old 2 r) (old 2 u) (slot 2 0) (slot 2 1) (add (.conjL (.conjR (.conjR (.conjR hr2)))) I) (.hyp (Or.inl rfl))
    have hS := agree_at (old 2 w) (old 2 l) (old 2 s) (old 2 u) (slot 2 0) (slot 2 1) (add (.conjL (.conjR (.conjR (.conjR hs2)))) I) (.hyp (Or.inl rfl))
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjR hS) _) (.impE (add (.conjL hR) _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .impE (add (.conjR hR) _) (.impE (add (.conjL hS) _) (.hyp (Or.inl rfl)))
  · let E := Formula.equal (slot 2 0) (old 2 l)
    have he : Derives (Context.add E Δ) E := .hyp (Or.inl rfl)
    have hR := StructuralListFieldSyntax.index_subst _ _ _ _ _ (eq_symm he) (add (.conjR (.conjR (.conjR (.conjR hr2)))) E)
    have hS := StructuralListFieldSyntax.index_subst _ _ _ _ _ (eq_symm he) (add (.conjR (.conjR (.conjR (.conjR hs2)))) E)
    exact last_fields (ZFContext.add hZ2 E) _ _ _ _ _ _ (add hw2 E) (add hiN E) hR hS

theorem snoc_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w u l L h r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (snoc w u l L h r)) (hs : Derives Γ (snoc w u l L h s)) : Derives Γ (.equal r s) :=
  StructuralListCodeInduction.unique hZ w L r s hw (.conjL (.conjR hr)) (.conjL (.conjR hs)) (snoc_agree hZ w u l L h r s hw hr hs)

theorem output_subst {m} {Γ : Context m} (w n r s : Fin m) (he : Derives Γ (.equal r s))
    (hr : Derives Γ (reverses w n r)) : Derives Γ (reverses w n s) := by
  let P := reverses w.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate r = reverses w n r := by simp only [P,Formula.instantiate,reverses_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate s = reverses w n s := by simp only [P,Formula.instantiate,reverses_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (consCode w h t n))
    (ht : Derives Γ (hasLength w t l)) (hL : Derives Γ (successor L l))
    (hu : Derives Γ (reverses w t u)) (hr : Derives Γ (snoc w u l L h r)) : Derives Γ (reverses w n r) := by
  have hn := StructuralListValidity.cons_valid hZ w h t n hw hh (StructuralListLengthBasic.valid_of_length w t l ht) hc
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (reverses w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListReverseEncoding.exists_reverse hZ w n hw hn)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hc1 := of_eq (consCode_rename w h t n Fin.castSucc) (under hc R)
  have ht1 := of_eq (hasLength_rename w t l Fin.castSucc) (under ht R)
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL R)
  have hu1 := of_eq (reverses_rename w t u Fin.castSucc) (under hu R)
  have hr1 := of_eq (snoc_rename w u l L h r Fin.castSucc) (under hr R)
  have hActual := forward hZ1 w.castSucc h.castSucc t.castSucc n.castSucc l.castSucc L.castSucc u.castSucc (Fin.last m) hw1 hh1 hc1 ht1 hL1 hu1 (.conjR hR)
  have he := snoc_unique hZ1 _ _ _ _ _ _ _ hw1 hActual hr1
  simpa only [Formula.raise,reverses_rename] using output_subst _ _ _ _ he (.conjR hR)

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (consCode w h t n))
    (ht : Derives Γ (hasLength w t l)) (hL : Derives Γ (successor L l)) (hu : Derives Γ (reverses w t u)) :
    Derives Γ ((reverses w n r).iff (snoc w u l L h r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hh _) (add hc _) (add ht _) (add hL _) (add hu _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hh _) (add hc _) (add ht _) (add hL _) (add hu _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListReverseConsContract
