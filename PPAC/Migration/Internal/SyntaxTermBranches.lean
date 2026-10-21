import PPAC.Migration.Internal.SyntaxTermSyntax

/-! 纯项变量分支的真实索引范围、排他性、自然值域和唯一内部解码。 -/
namespace PPAC.Migration.Internal.SyntaxTermBranches
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxVariableSyntax SyntaxVariableDecodeSyntax SyntaxTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) (hb : Derives Γ (branch bound w l n)) : Derives Γ (.mem i l) := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hc1 : Derives Δ (code bound w.castSucc i.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have heq := SyntaxVariableDecode.index_eq (ZFContext.under hZ B) bound _ _ _ _ hw1 (.conjR hB) hc1
  exact mem_subst heq (.conjL hB)

theorem iff_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) : Derives Γ ((branch bound w l n).iff (.mem i l)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact member (ZFContext.add hZ _) bound _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_branch bound _ _ _ _ (.hyp (Or.inl rfl)) (add hc _)

theorem opposite {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) (hb : Derives Γ (branch (!bound) w l n)) : Derives Γ .bot := by
  let B := branchWitness (!bound) w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch (!bound) w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hc1 : Derives Δ (code bound w.castSucc i.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxVariableDecode.opposite_disjoint (ZFContext.under hZ B) bound _ _ _ _ hw1 hc1 (.conjR hB)

theorem exclusive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (branch true w b n)) (hf : Derives Γ (branch false w f n)) : Derives Γ .bot := by
  let B := branchWitness true w b n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch true w b n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hf1 : Derives Δ (branch false w.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, branch_rename] using under hf B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact opposite (ZFContext.under hZ B) true _ _ _ _ hw1 (.conjR hB) hf1

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (branch bound w l n)) : Derives Γ (.mem n w) := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxVariableDecode.range (ZFContext.under hZ B) bound _ _ _ hw1 (.conjR hB)

theorem decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (branch bound w l n)) : Derives Γ (decodedBranch bound w l n) := by
  let B := branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := SyntaxVariableDecode.unique_index (ZFContext.under hZ B) bound _ _ _ hw1 (.conjR hB)
  have hout := intro_decoded_branch bound _ _ _ _ (.conjL hB) (.conjR hB) hu
  simpa only [Formula.raise, decodedBranch_rename] using hout

theorem branch_of_decoded {m} {Γ : Context m} (bound : Bool) (w l n : Fin m)
    (hd : Derives Γ (decodedBranch bound w l n)) : Derives Γ (branch bound w l n) := by
  let D := decodedWitness bound w l n
  let Δ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := intro_branch bound _ _ _ _ (.conjL (.conjL hD)) (.conjR (.conjL hD))
  simpa only [Formula.raise, branch_rename] using hout

theorem decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((branch bound w l n).iff (decodedBranch bound w l n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decode (ZFContext.add hZ _) bound _ _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact branch_of_decoded bound _ _ _ (.hyp (Or.inl rfl))

theorem empty {m} {Γ : Context m} (bound : Bool) (w l n : Fin m) (hl : Derives Γ (OmegaSyntax.empty l)) : Derives Γ (branch bound w l n).neg := by
  apply Derives.impI
  let B := branchWitness bound w l n
  let Ξ := Context.add (branch bound w l n) Γ
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply eliminate_branch bound w l n _ (.hyp (Or.inl rfl))
  have hl1 : Derives Δ (OmegaSyntax.empty l.castSucc) := by simpa only [Formula.raise, empty_rename] using under (add hl (branch bound w l n)) B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (empty_at _ _ hl1) (.conjL hB)
end PPAC.Migration.Internal.SyntaxTermBranches
