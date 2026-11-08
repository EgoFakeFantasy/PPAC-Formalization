import PPAC.Migration.ForcingGuardCode

/-! Reuse the exact existing guard compiler for the domain predicate and the
inner r <= q guard of pinned Force.ex. In particular the latter is obtained
from the reverse relation followed by actual condition rebinding, so its
order is not accidentally q <= r. Not a complete existential step or Con. -/
namespace PPAC.Migration.ForcingExistGuardsCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 16384

/-- Ignore the second relation argument: the first argument is the HS name. -/
def domainOrder {n} (H : Source.Formula (n+1)) : Source.Formula (n+2) := H.rename Fin.castSucc

def reverseOrder {n} (R : Source.Formula (n+2)) : Source.Formula (n+2) := R.rename
  (Fin.lastCases (Fin.last n).castSucc (Fin.lastCases (Fin.last (n+1)) (fun i => i.castSucc.castSucc)))

theorem domain_relation {n m} (H : Source.Formula (n+1)) (rho : Fin n → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel (domainOrder H) rho x y = MinimalPredicates.pred H rho x := by
  simp only [domainOrder, ReplacementPredicates.rel, Source.SetLanguage.relation, MinimalPredicates.pred, rename_comp]
  congr 1
  funext i
  exact Fin.lastCases_castSucc i

theorem reverse_relation {n m} (R : Source.Formula (n+2)) (rho : Fin n → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel (reverseOrder R) rho x y = ReplacementPredicates.rel R rho y x := by
  simp only [reverseOrder, ReplacementPredicates.rel, Source.SetLanguage.relation, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

/-- H(x) uses the already accepted literal order-template code constructor. -/
def domainFiber {n m} (H : Source.Formula (n+1)) (w A f x : Fin m) : Formula m :=
  ForcingGuardCode.fiber true (domainOrder H) w A f x
private theorem domainFiber_rename {n m l} (H : Source.Formula (n+1)) (w A f x : Fin m) (r : Fin m → Fin l) :
    (domainFiber H w A f x).rename r = domainFiber H (r w) (r A) (r f) (r x) := by
  simp only [domainFiber, ForcingGuardCode.fiber, ForcingGuardCode.uniqueOutput, Formula.rename,
    ForcingGuardCode.compiled_rename, FormulaCodeSyntax.formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def domainAtNewName {n m} (H : Source.Formula (n+1)) (w A f : Fin m) : Formula m := existsMany 2
  ((SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)).conj
    (domainFiber H (old 2 w) (old 2 A) (old 2 f) (slot 2 1)))
private theorem domainAtNewName_rename {n m l} (H : Source.Formula (n+1)) (w A f : Fin m) (r : Fin m → Fin l) :
    (domainAtNewName H w A f).rename r = domainAtNewName H (r w) (r A) (r f) := by
  simp only [domainAtNewName, existsMany_rename, Formula.rename, SyntaxMixedImageHead.head_rename,
    domainFiber_rename, lift_old, lift_slot]

theorem domain_at_new_name_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (H : Source.Formula (n+1))
    (w a A f : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hs : Derives Γ (successor A a)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) :
    Derives Γ (domainAtNewName H w A f) := by
  let B := SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _
    (SyntaxMixedImageHead.exists_head hZ w a A f hw ha (SyntaxNumerals.range hZ (n+2) w f hw hf) hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hf2 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 2)) (HornBinderRules.under_body 2 hf B)
  have hD := ForcingGuardCode.fiber_total (HornBinderRules.zf_body 2 hZ B) true (domainOrder H)
    (old 2 w) (old 2 A) (old 2 f) (slot 2 1) hw2 hf2 (.conjR (.conjR hB))
  have ho : Derives Δ (domainAtNewName H (old 2 w) (old 2 A) (old 2 f)) := by
    apply HornBinderRules.intro_many 2 _ (slot 2)
    have hd : Derives Δ (B.conj (domainFiber H (old 2 w) (old 2 A) (old 2 f) (slot 2 1))) := .conjI hB hD
    exact of_eq (by simp only [B, Formula.rename, SyntaxMixedImageHead.head_rename, domainFiber_rename, assign_old, assign_slot]) hd
  exact of_eq (domainAtNewName_rename H w A f (old 2)).symm ho


private def data {n m} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w A f (v 0) (v 1)).conj
    ((ForcingGuardCode.compiled true (reverseOrder R) w A f (v 1) (v 2)).conj
      (ForcingConditionRebind.compiled w A f B j (v 2) Q))
private theorem data_rename {n m l} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (data R w A B f j Q v).rename r = data R (r w) (r A) (r B) (r f) (r j) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingGuardCode.compiled_rename, ForcingConditionRebind.compiled_rename]
private def body {n m} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) : Formula (m+3) :=
  data R (old 3 w) (old 3 A) (old 3 B) (old 3 f) (old 3 j) (old 3 Q) (slot 3)
/-- First R(p,q0), then rebind p to the new r0: exactly R(r0,q1). -/
def compiled {n m} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral (n+1) j).conj (existsMany 3 (body R w A B f j Q))
theorem compiled_rename {n m l} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) (r : Fin m → Fin l) :
    (compiled R w A B f j Q).rename r = compiled R (r w) (r A) (r B) (r f) (r j) (r Q) := by
  simp only [compiled, Formula.rename, SyntaxNumeralSyntax.numeral_rename, existsMany_rename, body, data_rename, lift_old, lift_slot]
def existsCompiled {n m} (R : Source.Formula (n+2)) (w A B f j : Fin m) : Formula m := .ex
  (compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m))
private theorem existsCompiled_rename {n m l} (R : Source.Formula (n+2)) (w A B f j : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R w A B f j).rename r = existsCompiled R (r w) (r A) (r B) (r f) (r j) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs {m} (n : Nat) (Γ : Context m) (w a A B f j : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ha : Derives Γ (.mem a w)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)
private theorem underInputs {n m} {Γ : Context m} {w a A B f j : Fin m}
    (h : Inputs n Γ w a A B f j) (T : Formula (m+1)) :
    Inputs n (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T), under h.ha T,
    of_eq (successor_rename A a Fin.castSucc) (under h.hA T), of_eq (successor_rename B A Fin.castSucc) (under h.hB T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T)⟩
private theorem underInputs2 {n m} {Γ : Context m} {w a A B f j : Fin m}
    (h : Inputs n Γ w a A B f j) (T : Formula (m+2)) :
    Inputs n (Context.add T (raisedContext 2 Γ)) (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j) := by
  exact ⟨of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.hw T), HornBinderRules.under_body 2 h.ha T,
    of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 h.hA T),
    of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 h.hB T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 2)) (HornBinderRules.under_body 2 h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j (old 2)) (HornBinderRules.under_body 2 h.hj T)⟩

private theorem from_guard {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A B f j z x T : Fin m) (h : Inputs n Γ w a A B f j)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x))
    (hT : Derives Γ (ForcingGuardCode.compiled true (reverseOrder R) w A f x T)) :
    Derives Γ (existsCompiled R w A B f j) := by
  let P := ForcingConditionRebind.compiled w.castSucc A.castSucc f.castSucc B.castSucc j.castSucc T.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (ForcingConditionRebind.total hZ w A f B j T h.hw h.hB
    (ForcingGuardCode.compiled_type true (reverseOrder R) w A f x T hT))
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh P)
  have ht1 := of_eq (ForcingGuardCode.compiled_rename true (reverseOrder R) w A f x T Fin.castSucc) (under hT P)
  let v : Fin 3 → Fin (m+1) := Fin.cases z.castSucc (SetLanguage.args2 x.castSucc T.castSucc)
  have hd : Derives Δ (data R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m) v) := .conjI hh1 (.conjI ht1 hP)
  have hb : Derives Δ (existsMany 3 (body R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m))) := by
    apply HornBinderRules.intro_many 3 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  have hj := of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj P)
  have hc : Derives Δ (compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)) := .conjI hj hb
  have ho : Derives Δ (existsCompiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename R w A B f j Fin.castSucc).symm ho

private theorem from_head {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A B f j z x : Fin m) (h : Inputs n Γ w a A B f j)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x)) : Derives Γ (existsCompiled R w A B f j) := by
  let T := ForcingGuardCode.compiled true (reverseOrder R) w.castSucc A.castSucc f.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ true (reverseOrder R) w A f x h.hw h.hf (.conjR (.conjR hh)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh T)
  have ho := from_guard (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc z.castSucc x.castSucc (Fin.last m)
    (underInputs h T) hh1 hT
  exact of_eq (existsCompiled_rename R w A B f j Fin.castSucc).symm ho

theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A B f j : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)) :
    Derives Γ (existsCompiled R w A B f j) := by
  let T := SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ (SyntaxMixedImageHead.exists_head hZ w a A f hw ha (SyntaxNumerals.range hZ (n+2) w f hw hf) hA)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := from_head (HornBinderRules.zf_body 2 hZ T) R (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j)
    (slot 2 0) (slot 2 1) (underInputs2 ⟨hw,ha,hA,hB,hf,hj⟩ T) hT
  exact of_eq (existsCompiled_rename R w A B f j (old 2)).symm ho

theorem compiled_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w A B f j Q : Fin m)
    (h : Derives Γ (compiled R w A B f j Q)) : Derives Γ (FormulaCodeSyntax.formulaCode w Q B f) := by
  let T := body R w A B f j Q
  let Δ := Context.add T (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 T _ (.conjR h)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w Q B f (old 3)).symm
    (ForcingConditionRebind.compiled_type (old 3 w) (old 3 A) (old 3 f) (old 3 B) (old 3 j) (slot 3 2) (old 3 Q) (.conjR (.conjR hT)))


private theorem guard_input_subst {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w A f x y T : Fin m)
    (he : Derives Γ (.equal x y)) (h : Derives Γ (ForcingGuardCode.compiled true (reverseOrder R) w A f x T)) :
    Derives Γ (ForcingGuardCode.compiled true (reverseOrder R) w A f y T) := by
  let P := ForcingGuardCode.compiled true (reverseOrder R) w.castSucc A.castSucc f.castSucc (Fin.last m) T.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
private theorem rebind_input_subst {m} {Γ : Context m} (w A B f j T U Q : Fin m)
    (he : Derives Γ (.equal T U)) (h : Derives Γ (ForcingConditionRebind.compiled w A f B j T Q)) :
    Derives Γ (ForcingConditionRebind.compiled w A f B j U Q) := by
  let P := ForcingConditionRebind.compiled w.castSucc A.castSucc f.castSucc B.castSucc j.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingConditionRebind.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingConditionRebind.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
private theorem data_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w A B f j Q V : Fin m) (xs ys : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data R w A B f j Q xs)) (hy : Derives Γ (data R w A B f j V ys)) : Derives Γ (.equal Q V) := by
  have hhx := Derives.conjL hx
  have hhy := Derives.conjL hy
  have hz := OmegaUniversal.empty_unique (xs 0) (ys 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL hhx) (.conjL hhy)
  have hc := AbstractVariableIndex.code_index_subst true w (xs 0) (ys 0) (xs 1) hz (.conjL (.conjR hhx))
  have he := SyntaxVariables.unique hZ true w (ys 0) (xs 1) (ys 1) hw hc (.conjL (.conjR hhy))
  have ht := guard_input_subst R w A f (xs 1) (ys 1) (xs 2) he (.conjL (.conjR hx))
  have hT := ForcingGuardCode.unique hZ true (reverseOrder R) w A f (ys 1) (xs 2) (ys 2) hw ht (.conjL (.conjR hy))
  have hq := rebind_input_subst w A B f j (xs 2) (ys 2) Q hT (.conjR (.conjR hx))
  exact ForcingConditionRebind.unique hZ w A f B j (ys 2) Q V hw hq (.conjR (.conjR hy))

theorem unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w A B f j Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled R w A B f j Q)) (hv : Derives Γ (compiled R w A B f j V)) : Derives Γ (.equal Q V) := by
  let T := body R w A B f j Q
  let Δ := Context.add T (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 T _ (.conjR hq)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename R w A B f j V (old 3)) (HornBinderRules.under_body 3 hv T)
  let U := body R (old 3 w) (old 3 A) (old 3 B) (old 3 f) (old 3 j) (old 3 V)
  let Ξ := Context.add U (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 U _ (.conjR hv1)
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 3 (old 3 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hw T) U)
  have hx2 : Derives Ξ (data R (old 3 (old 3 w)) (old 3 (old 3 A)) (old 3 (old 3 B)) (old 3 (old 3 f))
      (old 3 (old 3 j)) (old 3 (old 3 Q)) (fun i => old 3 (slot 3 i))) :=
    of_eq (by simp only [T, body, data_rename]) (HornBinderRules.under_body 3 hT U)
  exact data_unique (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 3 hZ T) U) R
    (old 3 (old 3 w)) (old 3 (old 3 A)) (old 3 (old 3 B)) (old 3 (old 3 f)) (old 3 (old 3 j))
    (old 3 (old 3 Q)) (old 3 (old 3 V)) (fun i => old 3 (slot 3 i)) (slot 3) hw2 hx2 hU

def uniqueOutput {n m} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) : Formula m := .all
  ((compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
private theorem uniqueOutput_rename {n m l} (R : Source.Formula (n+2)) (w A B f j Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R w A B f j Q).rename r = uniqueOutput R (r w) (r A) (r B) (r f) (r j) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w A B f j Q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R w A B f j Q)) :
    Derives Γ (uniqueOutput R w A B f j Q) := by
  apply Derives.allI
  apply Derives.impI
  let T := compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ T) R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (.hyp (Or.inl rfl))
    (of_eq (compiled_rename R w A B f j Q Fin.castSucc) (under hq T))

def fiber {n m} (R : Source.Formula (n+2)) (w A B f j : Fin m) : Formula m := .ex
  ((compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)).conj
    ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) B.castSucc f.castSucc).conj
      (uniqueOutput R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m))))
private theorem fiber_rename {n m l} (R : Source.Formula (n+2)) (w A B f j : Fin m) (r : Fin m → Fin l) :
    (fiber R w A B f j).rename r = fiber R (r w) (r A) (r B) (r f) (r j) := by
  simp only [fiber, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A B f j : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)) :
    Derives Γ (fiber R w A B f j) := by
  let T := compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (total hZ R w a A B f j hw ha hA hB hf hj)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := compiled_type R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m) hT
  have hu := unique_output (ZFContext.under hZ T) R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hT
  have ho : Derives Δ (fiber R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT (.conjI ht hu))
  exact of_eq (fiber_rename R w A B f j Fin.castSucc).symm ho

def sentence {n m} (R : Source.Formula (n+2)) (w a A B f j : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((successor B A).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp ((SyntaxNumeralSyntax.numeral (n+1) j).imp (fiber R w A B f j))))))).close

theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (w a A B f j : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R w a A B f j)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) R w a A B f j
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def domainSentence {n m} (H : Source.Formula (n+1)) (w a A f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp (domainAtNewName H w A f))))).close

theorem domain_kernel_certificate {n m} (H : Source.Formula (n+1)) (w a A f : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (domainSentence H w a A f)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact domain_at_new_name_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) H w a A f
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def uniqueSentence {n m} (R : Source.Formula (n+2)) (w A B f j Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled R w A B f j Q).imp ((compiled R w A B f j V).imp (.equal Q V)))).close
theorem unique_kernel_certificate {n m} (R : Source.Formula (n+2)) (w A B f j Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence R w A B f j Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    R w A B f j Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingExistGuardsCode
