import PPAC.Migration.ForcingAtomicCode
import PPAC.Migration.ForcingFormula
import PPAC.Migration.Internal.SyntaxAtomCases
import PPAC.Migration.Internal.FormulaCodeRecursive

/-! Actual four-way original atomic-code dispatch. Membership/equality are
compiled by the literal migrated forcing operation, with parsed fields inside
object existentials. Constants retain their native code; truth normalization
must be justified against the existing source forcing basis. This is the atomic
branch of the all-code interpretation, not a complete formula/Proof/Con result. -/
namespace PPAC.Migration.ForcingAtomCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 16384

private def memberMatrix {k m} (R : Formula (k+2)) (w a z n q : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (SyntaxAtomSyntax.memberAt w a z (v 0) (v 1) (v 2) n).conj
    (ForcingAtomicCode.compiled false R w a (v 1) (v 2) q)

private def equalMatrix {k m} (R : Formula (k+2)) (w a z n q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (SyntaxAtomSyntax.equalAt w a z (v 0) (v 1) n).conj
    (ForcingAtomicCode.compiled true R w a (v 0) (v 1) q)

private theorem memberMatrix_rename {k m l} (R : Formula (k+2)) (w a z n q : Fin m)
    (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (memberMatrix R w a z n q v).rename r = memberMatrix R (r w) (r a) (r z) (r n) (r q) (fun i => r (v i)) := by
  simp only [memberMatrix, Formula.rename, SyntaxAtomSyntax.memberAt_rename, ForcingAtomicCode.compiled_rename]

private theorem equalMatrix_rename {k m l} (R : Formula (k+2)) (w a z n q : Fin m)
    (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (equalMatrix R w a z n q v).rename r = equalMatrix R (r w) (r a) (r z) (r n) (r q) (fun i => r (v i)) := by
  simp only [equalMatrix, Formula.rename, SyntaxAtomSyntax.equalAt_rename, ForcingAtomicCode.compiled_rename]

private def memberBody {k m} (R : Formula (k+2)) (w a z n q : Fin m) : Formula (m+3) :=
  memberMatrix R (old 3 w) (old 3 a) (old 3 z) (old 3 n) (old 3 q) (slot 3)

private def equalBody {k m} (R : Formula (k+2)) (w a z n q : Fin m) : Formula (m+2) :=
  equalMatrix R (old 2 w) (old 2 a) (old 2 z) (old 2 n) (old 2 q) (slot 2)

private def constant {m} (w a z n q : Fin m) : Formula m :=
  ((SyntaxAtomSyntax.nullary false w a z n).disj (SyntaxAtomSyntax.nullary true w a z n)).conj (.equal q n)

private theorem constant_rename {m l} (w a z n q : Fin m) (r : Fin m → Fin l) :
    (constant w a z n q).rename r = constant (r w) (r a) (r z) (r n) (r q) := by
  simp only [constant, Formula.rename, SyntaxAtomSyntax.nullary_rename]

/-- All parsed term fields and all atomic compiler executions are object witnesses. -/
def compiled {k m} (R : Formula (k+2)) (w a z n q : Fin m) : Formula m :=
  (constant w a z n q).disj
    ((existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q)))

theorem compiled_rename {k m l} (R : Formula (k+2)) (w a z n q : Fin m) (r : Fin m → Fin l) :
    (compiled R w a z n q).rename r = compiled R (r w) (r a) (r z) (r n) (r q) := by
  simp only [compiled, Formula.rename, constant_rename, existsMany_rename,
    memberBody, equalBody, memberMatrix_rename, equalMatrix_rename, lift_old, lift_slot]

def existsCompiled {k m} (R : Formula (k+2)) (w a z n : Fin m) : Formula m := .ex
  (compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m))

private theorem existsCompiled_rename {k m l} (R : Formula (k+2)) (w a z n : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R w a z n).rename r = existsCompiled R (r w) (r a) (r z) (r n) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_member {k m} {Γ : Context m} (R : Formula (k+2)) (w a z n q s x y : Fin m)
    (hn : Derives Γ (SyntaxAtomSyntax.memberAt w a z s x y n))
    (hq : Derives Γ (ForcingAtomicCode.compiled false R w a x y q)) :
    Derives Γ (compiled R w a z n q) := by
  apply Derives.disjR
  apply Derives.disjL
  let v := SyntaxAtomSyntax.three s x y
  apply HornBinderRules.intro_many 3 _ v
  exact of_eq (by simp only [memberBody, memberMatrix_rename, assign_old, assign_slot]; rfl) (.conjI hn hq)

private theorem intro_equal {k m} {Γ : Context m} (R : Formula (k+2)) (w a z n q x y : Fin m)
    (hn : Derives Γ (SyntaxAtomSyntax.equalAt w a z x y n))
    (hq : Derives Γ (ForcingAtomicCode.compiled true R w a x y q)) :
    Derives Γ (compiled R w a z n q) := by
  apply Derives.disjR
  apply Derives.disjR
  let v := SyntaxAtomSyntax.two x y
  apply HornBinderRules.intro_many 2 _ v
  exact of_eq (by simp only [equalBody, equalMatrix_rename, assign_old, assign_slot]; rfl) (.conjI hn hq)

private theorem intro_exists {k m} {Γ : Context m} (R : Formula (k+2)) (w a z n q : Fin m)
    (hq : Derives Γ (compiled R w a z n q)) : Derives Γ (existsCompiled R w a z n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

private theorem from_member_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n s x y : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (SyntaxAtomSyntax.memberAt w a z s x y n)) : Derives Γ (existsCompiled R w a z n) := by
  have he := ForcingAtomicCode.total hZ false R w a z x y hw hz (.conjL (.conjR (.conjL hn))) (.conjR (.conjR (.conjL hn)))
  let B := ForcingAtomicCode.compiled false R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)
  apply Derives.exE (p := B) he
  have hn1 := of_eq (SyntaxAtomSyntax.memberAt_rename w a z s x y n Fin.castSucc) (under hn B)
  have ho := intro_exists R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)
    (intro_member R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) s.castSucc x.castSucc y.castSucc hn1 (.hyp (Or.inl rfl)))
  exact of_eq (existsCompiled_rename R w a z n Fin.castSucc).symm ho

private theorem from_equal_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n x y : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (SyntaxAtomSyntax.equalAt w a z x y n)) : Derives Γ (existsCompiled R w a z n) := by
  have he := ForcingAtomicCode.total hZ true R w a z x y hw hz (.conjL (.conjL hn)) (.conjR (.conjL hn))
  let B := ForcingAtomicCode.compiled true R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)
  apply Derives.exE (p := B) he
  have hn1 := of_eq (SyntaxAtomSyntax.equalAt_rename w a z x y n Fin.castSucc) (under hn B)
  have ho := intro_exists R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)
    (intro_equal R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc hn1 (.hyp (Or.inl rfl)))
  exact of_eq (existsCompiled_rename R w a z n Fin.castSucc).symm ho

/-- Parse the ACTUAL full atomic formula code, with no supplied term fields. -/
theorem total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Formula (k+2)) (w a z n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (SyntaxAtomSyntax.atomic w a z n)) : Derives Γ (existsCompiled R w a z n) := by
  apply Derives.disjE hn
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact intro_exists R w a z n n (.disjL (.conjI (.disjL (.hyp (Or.inl rfl))) (.eqRefl n)))
    · exact intro_exists R w a z n n (.disjL (.conjI (.disjR (.hyp (Or.inl rfl))) (.eqRefl n)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · let C := SyntaxAtomSyntax.memberBody w a z n
      apply SyntaxAtomLogic.eliminate_member w a z n _ (.hyp (Or.inl rfl))
      let D := (SyntaxAtomSyntax.membership w a z n).disj (SyntaxAtomSyntax.equality w a z n)
      let Δ := Context.add (SyntaxAtomSyntax.membership w a z n) (Context.add D Γ)
      have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ D) _
      have hw1 : Derives Δ (omega w) := add (add hw D) _
      have hz1 : Derives Δ (empty z) := add (add hz D) _
      have hw3 : Derives (Context.add C (raisedContext 3 Δ)) (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw1 C)
      have hz3 : Derives (Context.add C (raisedContext 3 Δ)) (empty z.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxAtomLogic.under_three hz1 C)
      have ho := from_member_fields (SyntaxAtomLogic.zf_under_three hZ1 C) R w.castSucc.castSucc.castSucc
        a.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hz3 (.hyp (Or.inl rfl))
      exact of_eq (by simp only [Formula.raise, existsCompiled_rename]) ho
    · let C := SyntaxAtomSyntax.equalBody w a z n
      apply SyntaxAtomLogic.eliminate_equality w a z n _ (.hyp (Or.inl rfl))
      let D := (SyntaxAtomSyntax.membership w a z n).disj (SyntaxAtomSyntax.equality w a z n)
      let Δ := Context.add (SyntaxAtomSyntax.equality w a z n) (Context.add D Γ)
      have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ D) _
      have hw1 : Derives Δ (omega w) := add (add hw D) _
      have hz1 : Derives Δ (empty z) := add (add hz D) _
      have hw2 : Derives (Context.add C (raisedContext 2 Δ)) (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw1 C)
      have hz2 : Derives (Context.add C (raisedContext 2 Δ)) (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (OrderedPairElimination.under_two hz1 C)
      have ho := from_equal_fields (ZFContext.under_two hZ1 C) R w.castSucc.castSucc a.castSucc.castSucc
        z.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hz2 (.hyp (Or.inl rfl))
      exact of_eq (by simp only [Formula.raise, existsCompiled_rename]) ho


private theorem typed_rename {m l} (k : Nat) (w a q : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicCode.typed k w a q).rename r = ForcingAtomicCode.typed k (r w) (r a) (r q) := by
  simp only [ForcingAtomicCode.typed, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    FormulaCodeSyntax.formulaCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem typed_output_subst {m} {Γ : Context m} (k : Nat) (w a n q : Fin m)
    (he : Derives Γ (.equal n q)) (hn : Derives Γ (ForcingAtomicCode.typed k w a n)) :
    Derives Γ (ForcingAtomicCode.typed k w a q) := by
  let F := ForcingAtomicCode.typed k w.castSucc a.castSucc (Fin.last m)
  exact of_eq (by simp only [F, Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn))

private theorem nullary_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w a z n f : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (.mem f w))
    (hn : Derives Γ (SyntaxAtomSyntax.nullary truth w a z n)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n a f) := by
  have hconst : Derives Γ (SyntaxAtomSyntax.nullary truth w a f n) := .conjI
    (.conjI (.conjL (.conjL hn)) hf) (.conjR hn)
  have hnw := SyntaxNodeInjective.constructor_range hZ 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n hw (.conjR hn)
  have hatom : Derives Γ (SyntaxAtomSyntax.atomic w a f n) := by
    cases truth
    · exact .disjL (.disjL hconst)
    · exact .disjL (.disjR hconst)
  exact .impE (.conjR (FormulaCodeRecursive.recursive_iff hZ w n a f hw)) (.conjI hnw (.disjL hatom))

private theorem nullary_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (k : Nat) (w a z n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.nullary truth w a z n)) : Derives Γ (ForcingAtomicCode.typed k w a n) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral (k+2) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ (k+2) w hw)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hn1 := of_eq (SyntaxAtomSyntax.nullary_rename truth w a z n Fin.castSucc) (under hn B)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht := nullary_type (ZFContext.under hZ B) truth w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) hw1 (.conjL hB) hn1
  have ho : Derives Δ (ForcingAtomicCode.typed k w.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxNumeralSyntax.numeral_rename, FormulaCodeSyntax.formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hB) ht)
  exact of_eq (typed_rename k w a n Fin.castSucc).symm ho

private theorem constant_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w a z n q : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (constant w a z n q)) :
    Derives Γ (ForcingAtomicCode.typed k w a q) := by
  apply Derives.disjE (.conjL hn)
  · exact typed_output_subst k w a n q (eq_symm (add (.conjR hn) _))
      (nullary_typed (ZFContext.add hZ _) false k w a z n (add hw _) (.hyp (Or.inl rfl)))
  · exact typed_output_subst k w a n q (eq_symm (add (.conjR hn) _))
      (nullary_typed (ZFContext.add hZ _) true k w a z n (add hw _) (.hyp (Or.inl rfl)))

theorem compiled_type {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Formula (k+2))
    (w a z n q : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (compiled R w a z n q)) :
    Derives Γ (ForcingAtomicCode.typed k w a q) := by
  apply Derives.disjE hn
  · exact constant_type (ZFContext.add hZ _) k w a z n q (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · let B := memberBody R w a z n q
      apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
      let D := (existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q))
      let Δ := Context.add (existsMany 3 B) (Context.add D Γ)
      have hB : Derives (Context.add B (raisedContext 3 Δ)) B := .hyp (Or.inl rfl)
      have ht := ForcingAtomicCode.compiled_type false R (old 3 w) (old 3 a)
        (slot 3 1) (slot 3 2) (old 3 q) (.conjR hB)
      exact of_eq (typed_rename k w a q (old 3)).symm ht
    · let B := equalBody R w a z n q
      apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
      let D := (existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q))
      let Δ := Context.add (existsMany 2 B) (Context.add D Γ)
      have hB : Derives (Context.add B (raisedContext 2 Δ)) B := .hyp (Or.inl rfl)
      have ht := ForcingAtomicCode.compiled_type true R (old 2 w) (old 2 a)
        (slot 2 0) (slot 2 1) (old 2 q) (.conjR hB)
      exact of_eq (typed_rename k w a q (old 2)).symm ht

/-- Reverse of native truth is the original source formula bottom -> bottom.
Its forcing is a pure logical truth; keeping the native truth code is justified
by this object derivation, rather than an assumed normalization law. -/
def truthNormalizationSentence {k m} (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (P p : Fin m) : Source.Sentence :=
  ((ForcingFormula.formula R H rho (Fin.elim0 : Fin 0 → Fin m) P p (.imp .bot .bot)).iff (.imp .bot .bot)).close

theorem truth_normalization_kernel_certificate {k m} (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (P p : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (truthNormalizationSentence R H rho P p)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  · apply Derives.impI
    apply Derives.allI
    apply Derives.impI
    apply Derives.impI
    apply Derives.impI
    exact .conjL (.hyp (Or.inl rfl))


private theorem member_source {k m} {Γ : Context m} (R : Formula (k+2)) (w a z n q : Fin m)
    (h : Derives Γ (existsMany 3 (memberBody R w a z n q))) : Derives Γ (SyntaxAtomSyntax.membership w a z n) := by
  let B := memberBody R w a z n q
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxAtomSyntax.membership_rename w a z n (old 3)).symm
    (SyntaxAtomLogic.intro_member (old 3 w) (old 3 a) (old 3 z) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) (.conjL hB))

private theorem equal_source {k m} {Γ : Context m} (R : Formula (k+2)) (w a z n q : Fin m)
    (h : Derives Γ (existsMany 2 (equalBody R w a z n q))) : Derives Γ (SyntaxAtomSyntax.equality w a z n) := by
  let B := equalBody R w a z n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxAtomSyntax.equality_rename w a z n (old 2)).symm
    (SyntaxAtomLogic.intro_equality (old 2 w) (old 2 a) (old 2 z) (slot 2 0) (slot 2 1) (old 2 n) (.conjL hB))

private theorem constant_member_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a z n q : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constant w a z n q))
    (hm : Derives Γ (SyntaxAtomSyntax.membership w a z n)) : Derives Γ .bot := by
  apply Derives.disjE (.conjL hc)
  · exact SyntaxAtomCases.member_conflict (ZFContext.add hZ _) 0 0 (by decide) w a z n Fin.elim0
      (add hw _) (.conjR (.hyp (Or.inl rfl))) (add hm _)
  · exact SyntaxAtomCases.member_conflict (ZFContext.add hZ _) 0 1 (by decide) w a z n Fin.elim0
      (add hw _) (.conjR (.hyp (Or.inl rfl))) (add hm _)

private theorem constant_equal_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a z n q : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constant w a z n q))
    (hm : Derives Γ (SyntaxAtomSyntax.equality w a z n)) : Derives Γ .bot := by
  apply Derives.disjE (.conjL hc)
  · exact SyntaxAtomCases.equal_conflict (ZFContext.add hZ _) 0 0 (by decide) w a z n Fin.elim0
      (add hw _) (.conjR (.hyp (Or.inl rfl))) (add hm _)
  · exact SyntaxAtomCases.equal_conflict (ZFContext.add hZ _) 0 1 (by decide) w a z n Fin.elim0
      (add hw _) (.conjR (.hyp (Or.inl rfl))) (add hm _)

private theorem atomic_terms_subst {k m} {Γ : Context m} (equality : Bool) (R : Formula (k+2))
    (w a x y u v q : Fin m) (hx : Derives Γ (.equal x u)) (hy : Derives Γ (.equal y v))
    (h : Derives Γ (ForcingAtomicCode.compiled equality R w a x y q)) :
    Derives Γ (ForcingAtomicCode.compiled equality R w a u v q) := by
  let F := ForcingAtomicCode.compiled equality R w.castSucc a.castSucc (Fin.last m) y.castSucc q.castSucc
  have h1 : Derives Γ (ForcingAtomicCode.compiled equality R w a u y q) :=
    of_eq (by simp only [F, Formula.instantiate, ForcingAtomicCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst F hx (of_eq (by simp only [F, Formula.instantiate, ForcingAtomicCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let G := ForcingAtomicCode.compiled equality R w.castSucc a.castSucc u.castSucc (Fin.last m) q.castSucc
  exact of_eq (by simp only [G, Formula.instantiate, ForcingAtomicCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst G hy (of_eq (by simp only [G, Formula.instantiate, ForcingAtomicCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))

private theorem constant_candidate {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n q v : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (constant w a z n q)) (hv : Derives Γ (compiled R w a z n v)) : Derives Γ (.equal q v) := by
  apply Derives.disjE hv
  · exact eq_trans (add (.conjR hq) _) (eq_symm (.conjR (.hyp (Or.inl rfl))))
  · let D := (existsMany 3 (memberBody R w a z n v)).disj (existsMany 2 (equalBody R w a z n v))
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (constant_member_conflict (ZFContext.add (ZFContext.add hZ D) _) w a z n q
        (add (add hw D) _) (add (add hq D) _) (member_source R w a z n v (.hyp (Or.inl rfl))))
    · exact .botE (constant_equal_conflict (ZFContext.add (ZFContext.add hZ D) _) w a z n q
        (add (add hw D) _) (add (add hq D) _) (equal_source R w a z n v (.hyp (Or.inl rfl))))

/-- Invert the actual member compilation at the original typed term fields. -/
theorem member_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n s x y q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberAt w a z s x y n))
    (hq : Derives Γ (compiled R w a z n q)) : Derives Γ (ForcingAtomicCode.compiled false R w a x y q) := by
  apply Derives.disjE hq
  · exact .botE (constant_member_conflict (ZFContext.add hZ _) w a z n q (add hw _) (.hyp (Or.inl rfl))
      (SyntaxAtomLogic.intro_member w a z s x y n (add hn _)))
  · let D := (existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q))
    apply Derives.disjE (.hyp (Or.inl rfl))
    · let B := memberBody R w a z n q
      let Δ := Context.add (existsMany 3 B) (Context.add D Γ)
      let Ξ := Context.add B (raisedContext 3 Δ)
      apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
      have hB : Derives Ξ B := .hyp (Or.inl rfl)
      have hZ3 : ZFContext.Evidence Ξ := HornBinderRules.zf_body 3 (ZFContext.add (ZFContext.add hZ D) _) B
      have hw3 : Derives Ξ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 (add (add hw D) _) B)
      have hn3 : Derives Ξ (SyntaxAtomSyntax.memberAt (old 3 w) (old 3 a) (old 3 z) (old 3 s) (old 3 x) (old 3 y) (old 3 n)) := of_eq (SyntaxAtomSyntax.memberAt_rename w a z s x y n (old 3)) (HornBinderRules.under_body 3 (add (add hn D) _) B)
      have he := SyntaxAtomUnique.member_fields hZ3 (old 3 w) (old 3 s) (old 3 x) (old 3 y)
        (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) hw3 (.conjR hn3) (.conjR (.conjL hB))
      apply of_eq (ForcingAtomicCode.compiled_rename false R w a x y q (old 3)).symm
      exact atomic_terms_subst false R (old 3 w) (old 3 a) (slot 3 1) (slot 3 2)
        (old 3 x) (old 3 y) (old 3 q) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) (.conjR hB)
    · have hn1 := add (add hn D) (existsMany 2 (equalBody R w a z n q))
      exact .botE (SyntaxAtomCases.equal_conflict (ZFContext.add (ZFContext.add hZ D) _) 3 2 (by decide)
        w a z n (SyntaxAtomSyntax.three s x y) (add (add hw D) _) (.conjR hn1)
        (equal_source R w a z n q (.hyp (Or.inl rfl))))

private theorem member_candidate {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n s x y q v : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberAt w a z s x y n))
    (hq : Derives Γ (ForcingAtomicCode.compiled false R w a x y q))
    (hv : Derives Γ (compiled R w a z n v)) : Derives Γ (.equal q v) :=
  ForcingAtomicCode.unique hZ false R w a x y q v hw hq
    (member_output hZ R w a z n s x y v hw hn hv)

/-- Invert the actual equal compilation at the original typed term fields. -/
theorem equal_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n x y q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalAt w a z x y n))
    (hq : Derives Γ (compiled R w a z n q)) : Derives Γ (ForcingAtomicCode.compiled true R w a x y q) := by
  apply Derives.disjE hq
  · exact .botE (constant_equal_conflict (ZFContext.add hZ _) w a z n q (add hw _) (.hyp (Or.inl rfl))
      (SyntaxAtomLogic.intro_equality w a z x y n (add hn _)))
  · let D := (existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q))
    apply Derives.disjE (.hyp (Or.inl rfl))
    · have hn1 := add (add hn D) (existsMany 3 (memberBody R w a z n q))
      exact .botE (SyntaxAtomCases.member_conflict (ZFContext.add (ZFContext.add hZ D) _) 2 3 (by decide)
        w a z n (SyntaxAtomSyntax.two x y) (add (add hw D) _) (.conjR hn1)
        (member_source R w a z n q (.hyp (Or.inl rfl))))
    · let B := equalBody R w a z n q
      let Δ := Context.add (existsMany 2 B) (Context.add D Γ)
      let Ξ := Context.add B (raisedContext 2 Δ)
      apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
      have hB : Derives Ξ B := .hyp (Or.inl rfl)
      have hZ2 : ZFContext.Evidence Ξ := HornBinderRules.zf_body 2 (ZFContext.add (ZFContext.add hZ D) _) B
      have hw2 : Derives Ξ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add (add hw D) _) B)
      have hn2 : Derives Ξ (SyntaxAtomSyntax.equalAt (old 2 w) (old 2 a) (old 2 z) (old 2 x) (old 2 y) (old 2 n)) := of_eq (SyntaxAtomSyntax.equalAt_rename w a z x y n (old 2)) (HornBinderRules.under_body 2 (add (add hn D) _) B)
      have he := SyntaxAtomUnique.equal_fields hZ2 (old 2 w) (old 2 x) (old 2 y) (slot 2 0) (slot 2 1) (old 2 n)
        hw2 (.conjR hn2) (.conjR (.conjL hB))
      apply of_eq (ForcingAtomicCode.compiled_rename true R w a x y q (old 2)).symm
      exact atomic_terms_subst true R (old 2 w) (old 2 a) (slot 2 0) (slot 2 1)
        (old 2 x) (old 2 y) (old 2 q) (eq_symm (.conjL he)) (eq_symm (.conjR he)) (.conjR hB)

private theorem equal_candidate {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w a z n x y q v : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalAt w a z x y n))
    (hq : Derives Γ (ForcingAtomicCode.compiled true R w a x y q))
    (hv : Derives Γ (compiled R w a z n v)) : Derives Γ (.equal q v) :=
  ForcingAtomicCode.unique hZ true R w a x y q v hw hq
    (equal_output hZ R w a z n x y v hw hn hv)

/-- Independent parsed fields, tag branches, and atomic executions agree. -/
theorem unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Formula (k+2)) (w a z n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R w a z n q)) (hv : Derives Γ (compiled R w a z n v)) :
    Derives Γ (.equal q v) := by
  apply Derives.disjE hq
  · exact constant_candidate (ZFContext.add hZ _) R w a z n q v (add hw _) (.hyp (Or.inl rfl)) (add hv _)
  · let D := (existsMany 3 (memberBody R w a z n q)).disj (existsMany 2 (equalBody R w a z n q))
    apply Derives.disjE (.hyp (Or.inl rfl))
    · let B := memberBody R w a z n q
      let Δ := Context.add (existsMany 3 B) (Context.add D Γ)
      let Ξ := Context.add B (raisedContext 3 Δ)
      apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
      have hB : Derives Ξ B := .hyp (Or.inl rfl)
      have hw3 : Derives Ξ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 (add (add hw D) _) B)
      have hv3 : Derives Ξ (compiled R (old 3 w) (old 3 a) (old 3 z) (old 3 n) (old 3 v)) := of_eq (compiled_rename R w a z n v (old 3)) (HornBinderRules.under_body 3 (add (add hv D) _) B)
      exact member_candidate (HornBinderRules.zf_body 3 (ZFContext.add (ZFContext.add hZ D) _) B) R
        (old 3 w) (old 3 a) (old 3 z) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 q) (old 3 v)
        hw3 (.conjL hB) (.conjR hB) hv3
    · let B := equalBody R w a z n q
      let Δ := Context.add (existsMany 2 B) (Context.add D Γ)
      let Ξ := Context.add B (raisedContext 2 Δ)
      apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
      have hB : Derives Ξ B := .hyp (Or.inl rfl)
      have hw2 : Derives Ξ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add (add hw D) _) B)
      have hv2 : Derives Ξ (compiled R (old 2 w) (old 2 a) (old 2 z) (old 2 n) (old 2 v)) := of_eq (compiled_rename R w a z n v (old 2)) (HornBinderRules.under_body 2 (add (add hv D) _) B)
      exact equal_candidate (HornBinderRules.zf_body 2 (ZFContext.add (ZFContext.add hZ D) _) B) R
        (old 2 w) (old 2 a) (old 2 z) (old 2 n) (slot 2 0) (slot 2 1) (old 2 q) (old 2 v)
        hw2 (.conjL hB) (.conjR hB) hv2


def uniqueOutput {k m} (R : Formula (k+2)) (w a z n q : Fin m) : Formula m := .all
  ((compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

private theorem uniqueOutput_rename {k m l} (R : Formula (k+2)) (w a z n q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R w a z n q).rename r = uniqueOutput R (r w) (r a) (r z) (r n) (r q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem unique_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Formula (k+2))
    (w a z n q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R w a z n q)) :
    Derives Γ (uniqueOutput R w a z n q) := by
  apply Derives.allI
  apply Derives.impI
  let B := compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hq1 := of_eq (compiled_rename R w a z n q Fin.castSucc) (under hq B)
  exact unique (ZFContext.under hZ B) R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) q.castSucc
    hw1 (.hyp (Or.inl rfl)) hq1

def fiber {k m} (R : Formula (k+2)) (w a z n : Fin m) : Formula m := .ex
  ((compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)).conj
    ((ForcingAtomicCode.typed k w.castSucc a.castSucc (Fin.last m)).conj
      (uniqueOutput R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m))))

private theorem fiber_rename {k m l} (R : Formula (k+2)) (w a z n : Fin m) (r : Fin m → Fin l) :
    (fiber R w a z n).rename r = fiber R (r w) (r a) (r z) (r n) := by
  simp only [fiber, Formula.rename, compiled_rename, typed_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Formula (k+2)) (w a z n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (SyntaxAtomSyntax.atomic w a z n)) :
    Derives Γ (fiber R w a z n) := by
  let B := compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (total hZ R w a z n hw hz hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht := compiled_type (ZFContext.under hZ B) R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) hw1 hB
  have hu := unique_output (ZFContext.under hZ B) R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m) hw1 hB
  have ho : Derives Δ (fiber R w.castSucc a.castSucc z.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, compiled_rename,
      typed_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB (.conjI ht hu))
  exact of_eq (fiber_rename R w a z n Fin.castSucc).symm ho

def sentence {k m} (R : Formula (k+2)) (w a z n : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxAtomSyntax.atomic w a z n).imp (fiber R w a z n)))).close

def uniqueSentence {k m} (R : Formula (k+2)) (w a z n q v : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled R w a z n q).imp ((compiled R w a z n v).imp (.equal q v)))).close

theorem kernel_certificate {k m} (R : Formula (k+2)) (w a z n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R w a z n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    R w a z n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_kernel_certificate {k m} (R : Formula (k+2)) (w a z n q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence R w a z n q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    R w a z n q v (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

/-- The existing constant candidate theorem fixes the actual atomic output
code; no source truth normalization or semantic claim is added here. -/
theorem nullary_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (R : Formula (k+2)) (w a z n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.nullary truth w a z n)) (hq : Derives Γ (compiled R w a z n q)) : Derives Γ (.equal q n) := by
  have hc : Derives Γ (constant w a z n n) := by
    apply Derives.conjI
    · cases truth
      · exact .disjL hn
      · exact .disjR hn
    · exact .eqRefl n
  exact eq_symm (constant_candidate hZ R w a z n n q hw hc hq)

end PPAC.Migration.ForcingAtomCode
