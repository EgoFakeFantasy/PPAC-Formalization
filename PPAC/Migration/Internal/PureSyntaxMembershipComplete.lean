import PPAC.Migration.Internal.PureSyntaxMembershipQuery

/-! 从完整Source成员原子实际构造纯公式查询；长度、参数森林及所有轨迹均对象存在。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_forest {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y args n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w b f (SyntaxAtomSyntax.two x y)))
    (hf : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hd := Derives.impE (.conjR (PureSyntaxMembershipType.at_forest_iff hZ w s x y args n hw hs hf)) hc
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have hZ1 := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw L)
  have hd1 : Derives Δ (PureSyntaxMembershipInput.data w.castSucc args.castSucc n.castSucc) := of_eq (PureSyntaxMembershipInput.data_rename _ _ _ Fin.castSucc) (under hd L)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc b.castSucc f.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq
    (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht L)
  have hf1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) args.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hf L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hctx := Derives.conjL (ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 0)
  have hlist := ArgumentForestTyping.list_of_forest hZ1 2 w.castSucc (Fin.last m) b.castSucc f.castSucc args.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) hw1 (.conjR hL) hctx hf1 ht1
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm
    (PureSyntaxMembershipQuery.checked_from_list hZ1 w.castSucc b.castSucc f.castSucc args.castSucc n.castSucc (Fin.last m) hw1 (.conjR hL) hlist hd1)

theorem checked_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hx : Derives Γ (SyntaxTermSyntax.term w b f x)) (hy : Derives Γ (SyntaxTermSyntax.term w b f y))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) : Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hxn := SyntaxTerms.range hZ w b f x hw hx
  have hyn := SyntaxTerms.range hZ w b f y hw hy
  have ht := ArgumentForestProgramSyntax.intro_typed 2 w b f (SyntaxAtomSyntax.two x y)
    (fun i => Fin.cases hx (fun j => Fin.cases hy (fun z => Fin.elim0 z) j) i)
  have hi := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two x y)
    (fun i => Fin.cases hxn (fun j => Fin.cases hyn (fun z => Fin.elim0 z) j) i)
  let A := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) (Fin.last m))
  let Δ := Context.add A (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex A) := of_eq (by simp only [A, SyntaxForestSyntax.existsForest, SyntaxAtomSyntax.two_map]) (SyntaxForests.exists_forest hZ 2 w (SyntaxAtomSyntax.two x y) hw hi)
  apply Derives.exE (p := A) he
  have hZ1 := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w.castSucc s.castSucc) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s Fin.castSucc) (under hs A)
  have hc1 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc s.castSucc x.castSucc y.castSucc n.castSucc) := of_eq (SyntaxAtomSyntax.memberCode_rename _ _ _ _ _ Fin.castSucc) (under hc A)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc b.castSucc f.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq
    (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm
    (at_forest hZ1 w.castSucc b.castSucc f.castSucc s.castSucc x.castSucc y.castSucc (Fin.last m) n.castSucc hw1 hs1 hc1 ht1 (.conjR hA))

theorem typed_membership_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s)) (hc : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hp := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w b f s x y n hw hc)) ht
  exact checked_at hZ w b f s x y n hw hs (.conjL (.conjR hp)) (.conjR (.conjR hp)) hc

theorem checked_membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxAtomSyntax.membership w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let B := SyntaxAtomSyntax.memberBody w b f n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply SyntaxAtomLogic.eliminate_member w b f n _ ht
  have hZ3 := HornBinderRules.zf_body 3 hZ B
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := checked_at hZ3 (old 3 w) (old 3 b) (old 3 f) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) hw3 (.conjL (.conjL hB)) (.conjL (.conjR (.conjL hB))) (.conjR (.conjR (.conjL hB))) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.formula_rename, old]) ho

end PPAC.Migration.Internal.PureSyntaxMembershipComplete
