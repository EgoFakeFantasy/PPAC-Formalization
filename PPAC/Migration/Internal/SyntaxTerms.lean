import PPAC.Migration.Internal.SyntaxTermBranches

/-! 纯项作用域的精确双条件、实际码构造、值域与实际唯一索引解码。 -/
namespace PPAC.Migration.Internal.SyntaxTerms
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxVariableSyntax SyntaxTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w b f n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) (ht : Derives Γ (term w b f n)) : Derives Γ (.mem i (limit bound b f)) := by
  cases bound with
  | false =>
    apply Derives.disjE (Derives.conjR ht)
    · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ _) false _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    · exact SyntaxTermBranches.member (ZFContext.add hZ _) false _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl))
  | true =>
    apply Derives.disjE (Derives.conjR ht)
    · exact SyntaxTermBranches.member (ZFContext.add hZ _) true _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl))
    · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ _) true _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem scope_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w b f n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) : Derives Γ ((term w b f n).iff (scope bound w b f i)) := by
  apply Derives.conjI
  · apply Derives.impI
    have ht : Derives (Context.add (term w b f n) Γ) (term w b f n) := .hyp (Or.inl rfl)
    exact .conjI (.conjL ht) (member (ZFContext.add hZ _) bound _ _ _ _ _ (add hw _) (add hc _) ht)
  · apply Derives.impI
    exact intro_term bound _ _ _ _ _ (.hyp (Or.inl rfl)) (add hc _)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (term w b f n)) : Derives Γ (.mem n w) := by
  apply Derives.disjE (Derives.conjR ht)
  · exact SyntaxTermBranches.range (ZFContext.add hZ _) true _ _ _ (add hw _) (.hyp (Or.inl rfl))
  · exact SyntaxTermBranches.range (ZFContext.add hZ _) false _ _ _ (add hw _) (.hyp (Or.inl rfl))

theorem decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (term w b f n)) : Derives Γ (decoded w b f n) := by
  apply Derives.conjI (Derives.conjL ht)
  apply Derives.disjE (Derives.conjR ht)
  · exact .disjL (SyntaxTermBranches.decode (ZFContext.add hZ _) true _ _ _ (add hw _) (.hyp (Or.inl rfl)))
  · exact .disjR (SyntaxTermBranches.decode (ZFContext.add hZ _) false _ _ _ (add hw _) (.hyp (Or.inl rfl)))

theorem term_of_decoded {m} {Γ : Context m} (w b f n : Fin m)
    (hd : Derives Γ (decoded w b f n)) : Derives Γ (term w b f n) := by
  apply Derives.conjI (Derives.conjL hd)
  apply Derives.disjE (Derives.conjR hd)
  · exact .disjL (SyntaxTermBranches.branch_of_decoded true _ _ _ (.hyp (Or.inl rfl)))
  · exact .disjR (SyntaxTermBranches.branch_of_decoded false _ _ _ (.hyp (Or.inl rfl)))

theorem decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((term w b f n).iff (decoded w b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decode (ZFContext.add hZ _) _ _ _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact term_of_decoded _ _ _ _ (.hyp (Or.inl rfl))

theorem exists_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w b f i : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (scope bound w b f i)) : Derives Γ (existsAt bound w b f i) := by
  have hl : Derives Γ (.mem (limit bound b f) w) := by
    cases bound with
    | false => exact .conjR (.conjL hs)
    | true => exact .conjL (.conjL hs)
  have hi := StructuralListTraceOrder.member_member hZ w i (limit bound b f) hw hl (.conjR hs)
  have hn := SyntaxVariables.exists_code hZ bound w i hw hi
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  change Derives Γ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hs1 : Derives Δ (scope bound w.castSucc b.castSucc f.castSucc i.castSucc) := by simpa only [Formula.raise, scope_rename] using under hs N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have ht := intro_term bound _ _ _ _ _ hs1 (.conjR hN)
  have hout : Derives Δ (existsAt bound w.castSucc b.castSucc f.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, code_rename, term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) (.conjI (.conjR hN) ht)
  simpa only [Formula.raise, existsAt_rename] using hout

theorem reject_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w b f n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) (hi : Derives Γ (Formula.mem i (limit bound b f)).neg) : Derives Γ (term w b f n).neg := by
  apply Derives.impI
  exact .impE (add hi _) (member (ZFContext.add hZ _) bound _ _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem reject_empty_contexts {m} {Γ : Context m} (w b f n : Fin m)
    (hb : Derives Γ (OmegaSyntax.empty b)) (hf : Derives Γ (OmegaSyntax.empty f)) : Derives Γ (term w b f n).neg := by
  apply Derives.impI
  apply Derives.disjE (Derives.conjR (.hyp (Or.inl rfl)) : Derives (Context.add (term w b f n) Γ) ((branch true w b n).disj (branch false w f n)))
  · exact .impE (add (add (SyntaxTermBranches.empty true w b n hb) _) _) (.hyp (Or.inl rfl))
  · exact .impE (add (add (SyntaxTermBranches.empty false w f n hf) _) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxTerms
