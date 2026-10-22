import PPAC.Migration.Internal.SyntaxTermImagePrefixSyntax

/-! 源头槽扩展在全部内部候选上的零、后继、源域和目标项性质。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem shifted_empty_conflict {m} {Γ : Context m} (f a i q : Fin m)
    (hi : Derives Γ (empty i)) (hv : Derives Γ (shifted f a i q)) : Derives Γ .bot := by
  let B := shiftedBody f a i q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hi1 : Derives Δ (empty i.castSucc) := of_eq (empty_rename i Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (OmegaStructureAlgebra.successor_not_empty _ _ (.conjL (.conjR hB))) hi1

theorem zero_iff {m} {Γ : Context m} (f a z i q : Fin m) (hi : Derives Γ (empty i)) :
    Derives Γ ((value f a z i q).iff (Formula.equal q z)) := by
  apply Derives.conjI
  · apply Derives.impI
    let V := value f a z i q
    apply Derives.disjE (Derives.hyp (Or.inl rfl) : Derives (Context.add V Γ) V)
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (shifted_empty_conflict f a i q (add (add hi V) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .disjL (.conjI (add hi _) (.hyp (Or.inl rfl)))

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a z i q k : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w)) (hi : Derives Γ (successor i k))
    (hv : Derives Γ (value f a z i q)) : Derives Γ ((Formula.mem k a).conj (edge f k q)) := by
  apply Derives.disjE hv
  · exact .botE (.impE (add (OmegaStructureAlgebra.successor_not_empty i k hi) _) (.conjL (.hyp (Or.inl rfl))))
  · let V := shifted f a i q
    let B := shiftedBody f a i q
    let Δ := Context.add B (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw V) B)
    have hk1 : Derives Δ (.mem k.castSucc w.castSucc) := under (add hk V) B
    have hi1 : Derives Δ (successor i.castSucc k.castSucc) := of_eq (successor_rename i k Fin.castSucc) (under (add hi V) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have eq := SyntaxIndexLiftOrder.successor_injective hZ1 _ _ _ _ hw1 hk1 hi1 (.conjL (.conjR hB))
    have ho := Derives.conjI (mem_subst (eq_symm eq) (.conjL hB))
      (IterationValues.edge_subst_input _ _ _ _ (eq_symm eq) (.conjR (.conjR hB)))
    exact of_eq (by simp only [Formula.raise, Formula.rename, edge_rename]) ho

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a z i q k : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w)) (hi : Derives Γ (successor i k)) :
    Derives Γ ((value f a z i q).iff ((Formula.mem k a).conj (edge f k q))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) w f a z i q k (add hw _) (add hk _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have h : Derives (Context.add ((Formula.mem k a).conj (edge f k q)) Γ) ((Formula.mem k a).conj (edge f k q)) := .hyp (Or.inl rfl)
    exact .disjR (intro_shifted f a i q k (.conjL h) (add hi _) (.conjR h))

theorem source_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a z A i q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hA : Derives Γ (successor A a))
    (hv : Derives Γ (value f a z i q)) : Derives Γ (.mem i A) := by
  apply Derives.disjE hv
  · exact SyntaxIndexLiftOrder.zero_member (ZFContext.add hZ _) w a A i (add hw _) (add ha _) (add hA _) (.conjL (.hyp (Or.inl rfl)))
  · let V := shifted f a i q
    let B := shiftedBody f a i q
    let Δ := Context.add B (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw V) B)
    have ha1 : Derives Δ (.mem a.castSucc w.castSucc) := under (add ha V) B
    have hA1 : Derives Δ (successor A.castSucc a.castSucc) := of_eq (successor_rename A a Fin.castSucc) (under (add hA V) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hk := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 ha1 (.conjL hB)
    exact SyntaxIndexLiftOrder.successor_member hZ1 _ _ _ _ _ hw1 hk ha1 (.conjL hB) (.conjL (.conjR hB)) hA1

theorem target_type {m} {Γ : Context m} (w f a c d z i q : Fin m)
    (hf : Derives Γ (imageMap w f a c d)) (hz : Derives Γ (SyntaxTermSyntax.term w c d z))
    (hv : Derives Γ (value f a z i q)) : Derives Γ (SyntaxTermSyntax.term w c d q) := by
  apply Derives.disjE hv
  · have h : Derives (Context.add ((empty i).conj (Formula.equal q z)) Γ) ((empty i).conj (Formula.equal q z)) := .hyp (Or.inl rfl)
    exact SyntaxAtomLogic.term_output_subst _ _ _ _ _ (eq_symm (.conjR h)) (add hz _)
  · let V := shifted f a i q
    let B := shiftedBody f a i q
    let Δ := Context.add B (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under (add hf V) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact of_eq (SyntaxTermSyntax.term_rename w c d q Fin.castSucc).symm
      (SyntaxTermImageSyntax.image_type _ _ _ _ _ _ _ hf1 (.conjR (.conjR hB)))

end PPAC.Migration.Internal.SyntaxTermImagePrefixPoint
