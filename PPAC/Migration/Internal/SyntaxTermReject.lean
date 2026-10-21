import PPAC.Migration.Internal.SyntaxTerms
import PPAC.Migration.Internal.SyntaxNodeArity

/-! 纯签名项排除函数标签、错误字段数和裸scalar；实际解码的bound/free分支互斥。 -/
namespace PPAC.Migration.Internal.SyntaxTermReject
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxVariableSyntax SyntaxTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k label : Nat) (hlabel : label ≠ tag bound)
    (w l n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor k label w xs n)) (hb : Derives Γ (branch bound w l n)) : Derives Γ .bot := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hc1 : Derives Δ (constructor k label w.castSucc (fun i => (xs i).castSucc) n.castSucc) := by simpa only [Formula.raise, constructor_rename] using under hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxVariableDecode.other_tag (ZFContext.under hZ B) bound k label hlabel _ _ _ _ hw1 (.conjR hB) hc1

theorem other_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k label : Nat) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (w b f n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor k label w xs n)) : Derives Γ (term w b f n).neg := by
  apply Derives.impI
  apply Derives.disjE (Derives.conjR (.hyp (Or.inl rfl)) : Derives (Context.add (term w b f n) Γ) ((branch true w b n).disj (branch false w f n)))
  · exact branch_tag (ZFContext.add (ZFContext.add hZ _) _) true k label h0 w b n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))
  · exact branch_tag (ZFContext.add (ZFContext.add hZ _) _) false k label h1 w f n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))

theorem branch_arity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k : Nat) (hk : k ≠ 1)
    (w a l n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (node k w a xs n)) (hb : Derives Γ (branch bound w l n)) : Derives Γ .bot := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hc1 : Derives Δ (node k w.castSucc a.castSucc (fun i => (xs i).castSucc) n.castSucc) := by simpa only [Formula.raise, node_rename] using under hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxNodeArity.variable_wrong_arity (ZFContext.under hZ B) bound k hk _ _ _ _ _ hw1 hc1 (.conjR hB)

theorem wrong_arity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k ≠ 1)
    (w a b f n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (node k w a xs n)) : Derives Γ (term w b f n).neg := by
  apply Derives.impI
  apply Derives.disjE (Derives.conjR (.hyp (Or.inl rfl)) : Derives (Context.add (term w b f n) Γ) ((branch true w b n).disj (branch false w f n)))
  · exact branch_arity (ZFContext.add (ZFContext.add hZ _) _) true k hk w a b n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))
  · exact branch_arity (ZFContext.add (ZFContext.add hZ _) _) false k hk w a f n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))

theorem scalar {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.scalar w a n)) : Derives Γ (term w b f n).neg :=
  wrong_arity hZ 0 (by decide) w a b f n Fin.elim0 hw hc

theorem decoded_exclusive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (decodedBranch true w b n)) (hf : Derives Γ (decodedBranch false w f n)) : Derives Γ .bot :=
  SyntaxTermBranches.exclusive hZ w b f n hw (SyntaxTermBranches.branch_of_decoded true _ _ _ hb) (SyntaxTermBranches.branch_of_decoded false _ _ _ hf)
theorem raw_branch_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (label : Nat) (hlabel : label ≠ tag bound)
    (w l t p n : Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxNumeralSyntax.numeral label t)) (hp : Derives Γ (.mem p w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) (hb : Derives Γ (branch bound w l n)) : Derives Γ .bot := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have ht1 : Derives Δ (SyntaxNumeralSyntax.numeral label t.castSucc) := by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using under ht B
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc t.castSucc p.castSucc n.castSucc) := by simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under hr B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxVariableDecode.other_raw_tag (ZFContext.under hZ B) bound label hlabel _ _ _ _ _ hw1 ht1 (under hp B) (.conjR hB) hr1

theorem raw_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (label : Nat) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (w b f t p n : Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxNumeralSyntax.numeral label t))
    (hp : Derives Γ (.mem p w)) (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ (term w b f n).neg := by
  apply Derives.impI
  apply Derives.disjE (Derives.conjR (.hyp (Or.inl rfl)) : Derives (Context.add (term w b f n) Γ) ((branch true w b n).disj (branch false w f n)))
  · exact raw_branch_tag (ZFContext.add (ZFContext.add hZ _) _) true label h0 w b t p n (add (add hw _) _) (add (add ht _) _) (add (add hp _) _) (add (add hr _) _) (.hyp (Or.inl rfl))
  · exact raw_branch_tag (ZFContext.add (ZFContext.add hZ _) _) false label h1 w f t p n (add (add hw _) _) (add (add ht _) _) (add (add hp _) _) (add (add hr _) _) (.hyp (Or.inl rfl))
theorem unknown_raw_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 t).neg) (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 t).neg)
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ (term w b f n).neg := by
  have branch_bad (bound : Bool) (l : Fin m) : Derives Γ (branch bound w l n).neg := by
    apply Derives.impI
    let B := branchWitness bound w l n
    let Ξ := Context.add (branch bound w l n) Γ
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply eliminate_branch bound w l n _ (.hyp (Or.inl rfl))
    have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise := under (add hq (branch bound w l n)) B
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ (branch bound w l n)) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hbad : Derives Γ (SyntaxNumeralSyntax.numeral (tag bound) t).neg := by
      cases bound with
      | false => exact h1
      | true => exact h0
    have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral (tag bound) t.castSucc).neg := by
      simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using lift hbad
    have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc t.castSucc p.castSucc n.castSucc) := by
      simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using lift hr
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact SyntaxVariableDecode.unknown_raw_tag hZ1 bound _ _ _ _ _ hw1 (lift ht) (lift hp) hbad1 (.conjR hB) hr1
  apply Derives.impI
  apply Derives.disjE (Derives.conjR (.hyp (Or.inl rfl)) : Derives (Context.add (term w b f n) Γ) ((branch true w b n).disj (branch false w f n)))
  · exact .impE (add (add (branch_bad true b) _) _) (.hyp (Or.inl rfl))
  · exact .impE (add (add (branch_bad false f) _) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxTermReject
