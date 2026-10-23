import PPAC.Migration.Internal.TypedArgumentListElimination

/-! 原有类型列表的Nil/Cons对象构造；内部索引逐个分成真实零/后继而非宿主Nat。 -/
namespace PPAC.Migration.Internal.TypedArgumentListConstruction
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem term_output_subst {m} {Γ : Context m} (w a b x y : Fin m) (he : Derives Γ (.equal x y))
    (hx : Derives Γ (SyntaxTermSyntax.term w a b x)) : Derives Γ (SyntaxTermSyntax.term w a b y) := by
  let P := SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc (Fin.last m)
  have h0 : P.instantiate x = SyntaxTermSyntax.term w a b x := by simp only [P, Formula.instantiate, SyntaxTermSyntax.term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate y = SyntaxTermSyntax.term w a b y := by simp only [P, Formula.instantiate, SyntaxTermSyntax.term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

theorem nil_typed_fields {m} {Γ : Context m} (w z a b n : Fin m) (hz : Derives Γ (empty z)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.typedFields w z a b n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc z.castSucc.castSucc).conj (StructuralListFieldSyntax.field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (OrderedPairElimination.under_two hz A)
  exact .botE (.impE (empty_at _ _ hz2) (.conjL (.hyp (Or.inl rfl))))

theorem nil_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a b n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z a b n) :=
  .conjI (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (.conjI hctx (.conjI (.conjI (StructuralNil.range hZ w n hw hn) (StructuralListLengthConstruct.nil_length hZ w n z hw hn hz)) (nil_typed_fields w z a b n hz)))

theorem cons_typed_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w ell k a b h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxTermSyntax.term w a b h))
    (hT : Derives Γ (SyntaxMixedImageCodeSyntax.termList w ell a b t))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) (hs : Derives Γ (successor k ell)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.typedFields w k a b n) := by
  have hhN := SyntaxTerms.range hZ w a b h hw hh
  have htN : Derives Γ (.mem t w) := .conjL (.conjL (.conjR (.conjR hT)))
  have hkN := OmegaStructureAlgebra.successor_member w k ell (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hT) hs
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc k.castSucc.castSucc).conj (StructuralListFieldSyntax.field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two hp A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hh2 : Derives Δ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc h.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift hh)
  have hT2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc ell.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc t.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (lift hT)
  have hc2 : Derives Δ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (lift hc)
  have hs2 : Derives Δ (successor k.castSucc.castSucc ell.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hs)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hi := StructuralListTraceOrder.member_member hZ2 w.castSucc.castSucc (Fin.last m).castSucc k.castSucc.castSucc hw2 (lift hkN) (.conjL hA)
  have hcases := OmegaStructureAlgebra.decomposition_at w.castSucc.castSucc (Fin.last m).castSucc
    (OmegaStructureInduction.decomposition w.castSucc.castSucc (ZFContext.separation hZ2 OmegaStructureSyntax.splitMatrix) hw2) hi
  apply Derives.disjE hcases
  · let E := empty (Fin.last m).castSucc
    have heq := StructuralListFieldCons.zero_point (ZFContext.add hZ2 E) w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (add hw2 E) (add (lift hhN) E) (add (lift htN) E) (add hc2 E) (.hyp (Or.inl rfl)) (add (.conjR hA) E)
    exact term_output_subst _ _ _ _ _ (eq_symm heq) (add hh2 E)
  · let E := OmegaStructureSyntax.predecessor w.castSucc.castSucc (Fin.last m).castSucc
    let Q := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (successor (Fin.last m).castSucc.castSucc (Fin.last (m+2)))
    let Ξ := Context.add Q (Context.image Formula.raise (Context.add E Δ))
    apply Derives.exE (p := Q) (.hyp (Or.inl rfl))
    have hZ3 := ZFContext.under (ZFContext.add hZ2 E) Q
    have lift3 {p : Formula (m+2)} (hp : Derives Δ p) : Derives Ξ p.raise := under (add hp E) Q
    have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (lift3 hw2)
    have hT3 : Derives Ξ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc.castSucc ell.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ Fin.castSucc) (lift3 hT2)
    have hc3 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (lift3 hc2)
    have hs3 : Derives Ξ (successor k.castSucc.castSucc.castSucc ell.castSucc.castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (lift3 hs2)
    have hf3 : Derives Ξ (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ Fin.castSucc) (lift3 (.conjR hA))
    have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
    have hj := SyntaxIndexLiftOrder.predecessor_member hZ3 w.castSucc.castSucc.castSucc ell.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) hw3 (.conjL hT3) hs3 (lift3 (.conjL hA)) (.conjR hQ)
    have hf := StructuralListFieldCons.successor_forward hZ3 w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (lift3 (lift hhN)) (lift3 (lift htN)) (.conjL hQ) (.conjR hQ) hc3 hf3
    have hout := SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hT3 hj hf
    exact of_eq (SyntaxTermSyntax.term_rename w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc).symm hout

theorem cons_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w ell k a b h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxTermSyntax.term w a b h))
    (hT : Derives Γ (SyntaxMixedImageCodeSyntax.termList w ell a b t))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) (hs : Derives Γ (successor k ell)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n) := by
  have hhN := SyntaxTerms.range hZ w a b h hw hh
  have hk := OmegaStructureAlgebra.successor_member w k ell (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hT) hs
  have hlen := StructuralListLengthConstruct.cons_length hZ w h t n ell k hw hhN hc (.conjR (.conjL (.conjR (.conjR hT)))) hs
  exact .conjI hk (.conjI (.conjL (.conjR hT)) (.conjI (.conjI (StructuralConsCore.range hZ w h t n hw hc) hlen) (cons_typed_fields hZ w ell k a b h t n hw hh hT hc hs)))

end PPAC.Migration.Internal.TypedArgumentListConstruction
