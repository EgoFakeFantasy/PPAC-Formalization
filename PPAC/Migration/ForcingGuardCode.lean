import PPAC.Migration.ForcingAtomicCode
import PPAC.Migration.ForcingConditionRebind

/-! Actual guards in pinned ForcingQuotient.AtomicData.Force neg/ex branches.
The bound condition term is an internal input. Template/scopes/lists/output
are constructed inside ZF; no full forcing/proof/Con interpretation is claimed. -/
namespace PPAC.Migration.ForcingGuardCode
section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature
private def roles : (n : Nat) → VariableSubstitution ℒ
    (fo_bound_context (n+3)) (fo_bound_context 1) (fo_bound_context (n+2))
  | 0 => fun v => match v with
    | .here => .fvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .bvar .here
    | .there (.there (.there v)) => nomatch v
  | n+1 => fun v => match v with
    | .here => .fvar .here
    | .there v => by
      simpa only [fo_bound_context, List.replicate_succ] using (roles n v).weakenFree SetSort.set

def sourceTemplate {n} (order : Bool) (R : Source.Formula (n+2)) : Source.Formula (n+3) :=
  if order then ReplacementPredicates.rel R (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last (n+2)) (Fin.last (n+1)).castSucc
  else .mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc

/-- Literal q in P / R(q,p); only q is bound, parameters/P/p stay free. -/
def template {n} (order : Bool) (R : Source.Formula (n+2)) :
    PureSyntaxQuotation.Fm (fo_bound_context 1) (fo_bound_context (n+2)) :=
  (Translation.formula fo_bound_variable (sourceTemplate order R)).substituteMapped
    (roles n) (fun {sort} (v : FirstOrder.Variable ([] : FirstOrder.SortContext ℒ) sort) => nomatch v)

open FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)

private theorem member_roles (n : Nat) :
    ∃ entry : FirstOrder.Variable (fo_bound_context (n+2)) SetSort.set,
      entry.index = n ∧
      roles n (fo_bound_variable (Fin.last n).castSucc.castSucc) = .fvar entry ∧
      roles n (fo_bound_variable (Fin.last (n+2))) = .bvar .here := by
  induction n with
  | zero => exact ⟨.here, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨entry, hi, hp, hq⟩ := ih
    refine ⟨.there entry, congrArg Nat.succ hi, ?_, ?_⟩
    · change (roles n (fo_bound_variable (Fin.last n).castSucc.castSucc)).weakenFree SetSort.set = .fvar (.there entry)
      rw [hp]
      rfl
    · change (roles n (fo_bound_variable (Fin.last (n+2)))).weakenFree SetSort.set = .bvar .here
      rw [hq]
      rfl

/-- Literal original q∈P: bound index zero and the ORIGINAL free P slot n.
This finite native-template identity does not restrict any internal code. -/
theorem member_template_tree {n} (R : Source.Formula (n+2)) :
    PureSyntaxQuotation.formulaTree (template false R) =
      Tree.node 2 ([leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf n])]) := by
  obtain ⟨entry, hi, hp, hq⟩ := member_roles n
  change Tree.node 2 ([leaf 0,
    PureSyntaxQuotation.termTree (roles n (fo_bound_variable (Fin.last (n+2)))),
    PureSyntaxQuotation.termTree (roles n (fo_bound_variable (Fin.last n).castSucc.castSucc))]) = _
  rw [hq, hp]
  change Tree.node 2 ([leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf entry.index])]) = _
  rw [hi]

end Templates
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingAtomicCode (identityImages identityImages_rename)
set_option maxRecDepth 16384

def quotation {n m} (order : Bool) (R : Source.Formula (n+2)) (w t f N : Fin m) : Formula m :=
  PureQuotationTypedSyntax.formulaValue (template order R) w t f N

theorem quotation_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w t f N : Fin m) (r : Fin m → Fin l) :
    (quotation order R w t f N).rename r = quotation order R (r w) (r t) (r f) (r N) := by
  simp only [quotation, PureQuotationTypedSyntax.formulaValue, Formula.rename,
    PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

def matrix {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 (v 0)).conj
    ((quotation order R w (v 0) f (v 1)).conj
      ((SyntaxForestSyntax.forest 1 w (fun _ => x) (v 2)).conj
        ((SyntaxMixedImageCodeSyntax.termList w (v 0) a f (v 2)).conj
          ((identityImages w a f (v 3)).conj
            (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 2) (v 3) (v 0) f a f (v 1) q)))))

theorem matrix_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w a f x q : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (matrix order R w a f x q v).rename r = matrix order R (r w) (r a) (r f) (r x) (r q) (fun i => r (v i)) := by
  simp only [matrix, Formula.rename, SyntaxNumeralSyntax.numeral_rename, quotation_rename,
    SyntaxForestSyntax.forest_rename, SyntaxMixedImageCodeSyntax.termList_rename, identityImages_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def body {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q : Fin m) : Formula (m+4) :=
  matrix order R (old 4 w) (old 4 a) (old 4 f) (old 4 x) (old 4 q) (slot 4)

def compiled {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q : Fin m) : Formula m :=
  existsMany 4 (body order R w a f x q)

theorem compiled_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w a f x q : Fin m) (r : Fin m → Fin l) :
    (compiled order R w a f x q).rename r = compiled order R (r w) (r a) (r f) (r x) (r q) := by
  simp only [compiled, existsMany_rename, body, matrix_rename, lift_old, lift_slot]

def existsCompiled {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x : Fin m) : Formula m := .ex
  (compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m))

private theorem existsCompiled_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w a f x : Fin m) (r : Fin m → Fin l) :
    (existsCompiled order R w a f x).rename r = existsCompiled order R (r w) (r a) (r f) (r x) := by
  simp only [existsCompiled, Formula.rename, compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs {m} (n : Nat) (Γ : Context m) (w t f a x : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hx : Derives Γ (SyntaxTermSyntax.term w a f x)

private theorem underInputs {n m} {Γ : Context m} {w t f a x : Fin m}
    (h : Inputs n Γ w t f a x) (B : Formula (m+1)) :
    Inputs n (Context.add B (Context.image Formula.raise Γ)) w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw B),
    of_eq (SyntaxNumeralSyntax.numeral_rename 1 t Fin.castSucc) (under h.ht B),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf B),
    of_eq (SyntaxTermSyntax.term_rename w a f x Fin.castSucc) (under h.hx B)⟩

private theorem assemble {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (n+2)) (w t f a x N U V : Fin m)
    (h : Inputs n Γ w t f a x) (hN : Derives Γ (quotation order R w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U))
    (hV : Derives Γ (identityImages w a f V)) : Derives Γ (existsCompiled order R w a f x) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w U V t f a f N) :=
    .conjI (.conjR hN) (.conjI htU (ForcingAtomicCode.identityImages_typed w a f V hV))
  let B := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc U.castSucc V.castSucc t.castSucc f.castSucc a.castSucc f.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w U V t f a f N h.hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename order R w t f N Fin.castSucc) (under hN B)
  have hU1 := of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => x) U Fin.castSucc) (under hU B)
  have htU1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)
  have hV1 := of_eq (identityImages_rename w a f V Fin.castSucc) (under hV B)
  let v : Fin 4 → Fin (m+1) := Fin.cases t.castSucc (Fin.cases N.castSucc (SetLanguage.args2 U.castSucc V.castSucc))
  have hm : Derives Δ (matrix order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m) v) :=
    .conjI h1.ht (.conjI hN1 (.conjI hU1 (.conjI htU1 (.conjI hV1 hB))))
  have hc : Derives Δ (compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 4 _ v
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  have ho : Derives Δ (existsCompiled order R w.castSucc a.castSucc f.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename order R w a f x Fin.castSucc).symm ho

private theorem with_free_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (n+2)) (w t f a x N U : Fin m)
    (h : Inputs n Γ w t f a x) (hN : Derives Γ (quotation order R w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U)) : Derives Γ (existsCompiled order R w a f x) := by
  let B := identityImages w.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ForcingAtomicCode.identityImages_exists hZ w a f h.hw (.conjL (.conjL h.hx)) (.conjR (.conjL h.hx)))
  have ho := assemble (ZFContext.under hZ B) order R w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc N.castSucc U.castSucc (Fin.last m)
    (underInputs h B) (of_eq (quotation_rename order R w t f N Fin.castSucc) (under hN B))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => x) U Fin.castSucc) (under hU B))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)) (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename order R w a f x Fin.castSucc).symm ho

private theorem with_bound_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (n+2)) (w t f a x N : Fin m)
    (h : Inputs n Γ w t f a x) (hN : Derives Γ (quotation order R w t f N)) : Derives Γ (existsCompiled order R w a f x) := by
  have hn : ∀ i : Fin 1, Derives Γ (.mem ((fun _ => x) i) w) := fun _ => SyntaxTerms.range hZ w a f x h.hw h.hx
  have he := SyntaxForests.exists_forest hZ 1 w (fun _ => x) h.hw (SyntaxForestSyntax.intro_inputs 1 w (fun _ => x) hn)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => x.castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have htU := ForcingAtomicCode.bound_forest_typed (ZFContext.under hZ B) w.castSucc t.castSucc a.castSucc f.castSucc (Fin.last m)
    (fun _ => x.castSucc) h1.hw h1.ht (.conjL h1.hx) (fun _ => h1.hx) (.conjR hB)
  have ho := with_free_images (ZFContext.under hZ B) order R w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc N.castSucc (Fin.last m)
    h1 (of_eq (quotation_rename order R w t f N Fin.castSucc) (under hN B)) (.conjR hB) htU
  exact of_eq (existsCompiled_rename order R w a f x Fin.castSucc).symm ho

private theorem with_template {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (n+2)) (w t f a x : Fin m) (h : Inputs n Γ w t f a x) :
    Derives Γ (existsCompiled order R w a f x) := by
  have ht : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 1).length t) := by
    have e : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 1).length = 1 := List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k t)) e) h.ht
  have hf : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) := by
    have e : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 := List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k f)) e) h.hf
  have he := PureQuotationTypedFormulas.exists_typed hZ (template order R) w t f h.hw ht hf
  let B := quotation order R w.castSucc t.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have ho := with_bound_images (ZFContext.under hZ B) order R w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc (Fin.last m)
    (underInputs h B) (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename order R w a f x Fin.castSucc).symm ho

/-- Arbitrary internal bound scope and condition term. f is the exact fixed
parameter/P/p free scope, not an externally chosen compiler output. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (R : Source.Formula (n+2))
    (w a f x : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hx : Derives Γ (SyntaxTermSyntax.term w a f x)) : Derives Γ (existsCompiled order R w a f x) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have h1 : Inputs n Δ w.castSucc (Fin.last m) f.castSucc a.castSucc x.castSucc :=
    ⟨of_eq (omega_rename w Fin.castSucc) (under hw B), .conjR (.hyp (Or.inl rfl)),
      of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf B),
      of_eq (SyntaxTermSyntax.term_rename w a f x Fin.castSucc) (under hx B)⟩
  exact of_eq (existsCompiled_rename order R w a f x Fin.castSucc).symm
    (with_template (ZFContext.under hZ B) order R w.castSucc (Fin.last m) f.castSucc a.castSucc x.castSucc h1)

theorem compiled_type {n m} {Γ : Context m} (order : Bool) (R : Source.Formula (n+2))
    (w a f x q : Fin m) (hq : Derives Γ (compiled order R w a f x q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q a f) := by
  let B := body order R w a f x q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w q a f (old 4)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 4 w) (slot 4 2) (slot 4 3) (slot 4 0) (old 4 f)
      (old 4 a) (old 4 f) (slot 4 1) (old 4 q) (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))

private theorem mixed_subst {m} {Γ : Context m} (w a f q : Fin m) (xs ys : Fin 4 → Fin m)
    (he : ∀ i, Derives Γ (.equal (xs i) (ys i)))
    (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 2) (xs 3) (xs 0) f a f (xs 1) q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 2) (ys 3) (ys 0) f a f (ys 1) q) := by
  let P0 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (xs 2).castSucc (xs 3).castSucc (Fin.last m) f.castSucc a.castSucc f.castSucc (xs 1).castSucc q.castSucc
  have h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 2) (xs 3) (ys 0) f a f (xs 1) q) :=
    of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 (he 0) (of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (xs 2).castSucc (xs 3).castSucc (ys 0).castSucc f.castSucc a.castSucc f.castSucc (Fin.last m) q.castSucc
  have h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (xs 2) (xs 3) (ys 0) f a f (ys 1) q) :=
    of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 (he 1) (of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let P2 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) (xs 3).castSucc (ys 0).castSucc f.castSucc a.castSucc f.castSucc (ys 1).castSucc q.castSucc
  have h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 2) (xs 3) (ys 0) f a f (ys 1) q) :=
    of_eq (by simp only [P2, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P2 (he 2) (of_eq (by simp only [P2, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  let P3 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (ys 2).castSucc (Fin.last m) (ys 0).castSucc f.castSucc a.castSucc f.castSucc (ys 1).castSucc q.castSucc
  have h4 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (ys 2) (ys 3) (ys 0) f a f (ys 1) q) :=
    of_eq (by simp only [P3, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P3 (he 3) (of_eq (by simp only [P3, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h3))
  exact h4

private theorem matrix_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (n+2)) (w a f x q v : Fin m) (xs ys : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (matrix order R w a f x q xs))
    (hy : Derives Γ (matrix order R w a f x v ys)) : Derives Γ (.equal q v) := by
  have ht := SyntaxNumerals.unique hZ 1 (xs 0) (ys 0) (.conjL hx) (.conjL hy)
  have hNx := Derives.conjL (.conjR hx)
  have hNy := Derives.conjL (.conjR hy)
  have hN := PureQuotationSyntax.formula_unique hZ (template order R) w (xs 1) (ys 1) hw (.conjL hNx) (.conjL hNy)
  have hU := SyntaxForests.unique hZ 1 w (fun _ => x) (xs 2) (ys 2) hw
    (.conjL (.conjR (.conjR hx))) (.conjL (.conjR (.conjR hy)))
  have hV := ForcingAtomicCode.identityImages_unique hZ w a f (xs 3) (ys 3) hw
    (.conjL (.conjR (.conjR (.conjR (.conjR hx))))) (.conjL (.conjR (.conjR (.conjR (.conjR hy)))))
  have he : ∀ i, Derives Γ (.equal (xs i) (ys i)) := by
    intro i
    exact Fin.cases ht (Fin.cases hN (Fin.cases hU (Fin.cases hV (fun j => Fin.elim0 j)))) i
  have hq := mixed_subst w a f q xs ys he (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (ys 2) (ys 3) (ys 0) f a f (ys 1) q v hw hq
    (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))

theorem unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (R : Source.Formula (n+2))
    (w a f x q v : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled order R w a f x q)) (hv : Derives Γ (compiled order R w a f x v)) :
    Derives Γ (.equal q v) := by
  let B := body order R w a f x q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename order R w a f x v (old 4)) (HornBinderRules.under_body 4 hv B)
  let C := body order R (old 4 w) (old 4 a) (old 4 f) (old 4 x) (old 4 v)
  let Ξ := Context.add C (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 C _ hv1
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 4 (old 4 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 4 (HornBinderRules.under_body 4 hw B) C)
  have hx2 : Derives Ξ (matrix order R (old 4 (old 4 w)) (old 4 (old 4 a)) (old 4 (old 4 f))
      (old 4 (old 4 x)) (old 4 (old 4 q)) (fun i => old 4 (slot 4 i))) :=
    of_eq (by simp only [B, body, matrix_rename]) (HornBinderRules.under_body 4 hB C)
  exact matrix_unique (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 4 hZ B) C) order R
    (old 4 (old 4 w)) (old 4 (old 4 a)) (old 4 (old 4 f)) (old 4 (old 4 x))
    (old 4 (old 4 q)) (old 4 (old 4 v)) (fun i => old 4 (slot 4 i)) (slot 4) hw2 hx2 hC

def uniqueOutput {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q : Fin m) : Formula m := .all
  ((compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

private theorem uniqueOutput_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w a f x q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput order R w a f x q).rename r = uniqueOutput order R (r w) (r a) (r f) (r x) (r q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem unique_output {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (R : Source.Formula (n+2))
    (w a f x q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled order R w a f x q)) :
    Derives Γ (uniqueOutput order R w a f x q) := by
  apply Derives.allI
  apply Derives.impI
  let B := compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ B) order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m) q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (.hyp (Or.inl rfl))
    (of_eq (compiled_rename order R w a f x q Fin.castSucc) (under hq B))

def fiber {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x : Fin m) : Formula m := .ex
  ((compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)).conj
    ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) a.castSucc f.castSucc).conj
      (uniqueOutput order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m))))

private theorem fiber_rename {n m l} (order : Bool) (R : Source.Formula (n+2))
    (w a f x : Fin m) (r : Fin m → Fin l) :
    (fiber order R w a f x).rename r = fiber order R (r w) (r a) (r f) (r x) := by
  simp only [fiber, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename,
    uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (R : Source.Formula (n+2))
    (w a f x : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hx : Derives Γ (SyntaxTermSyntax.term w a f x)) : Derives Γ (fiber order R w a f x) := by
  let B := compiled order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (total hZ order R w a f x hw hf hx)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := compiled_type order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m) hB
  have hu := unique_output (ZFContext.under hZ B) order R w.castSucc a.castSucc f.castSucc x.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) hB
  have ho : Derives Δ (fiber order R w.castSucc a.castSucc f.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB (.conjI ht hu))
  exact of_eq (fiber_rename order R w a f x Fin.castSucc).symm ho

def sentence {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp
    ((SyntaxTermSyntax.term w a f x).imp (fiber order R w a f x)))).close

def uniqueSentence {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q v : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled order R w a f x q).imp ((compiled order R w a f x v).imp (.equal q v)))).close

theorem kernel_certificate {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence order R w a f x)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    order R w a f x (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_kernel_certificate {n m} (order : Bool) (R : Source.Formula (n+2)) (w a f x q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence order R w a f x q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    order R w a f x q v (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))


/-- Both literal guards use the same internally constructed new bound condition.
Every head and both typed-unique outputs remain object existential. -/
def boundGuards {n m} (R : Source.Formula (n+2)) (w A f : Fin m) : Formula m := existsMany 2
  ((SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)).conj
    ((fiber false R (old 2 w) (old 2 A) (old 2 f) (slot 2 1)).conj
      (fiber true R (old 2 w) (old 2 A) (old 2 f) (slot 2 1))))

private theorem boundGuards_rename {n m l} (R : Source.Formula (n+2)) (w A f : Fin m) (r : Fin m → Fin l) :
    (boundGuards R w A f).rename r = boundGuards R (r w) (r A) (r f) := by
  simp only [boundGuards, existsMany_rename, Formula.rename, SyntaxMixedImageHead.head_rename,
    fiber_rename, lift_old, lift_slot]

theorem bound_guards_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hs : Derives Γ (successor A a)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) :
    Derives Γ (boundGuards R w A f) := by
  let B := SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _
    (SyntaxMixedImageHead.exists_head hZ w a A f hw ha (SyntaxNumerals.range hZ (n+2) w f hw hf) hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hf2 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 2)) (HornBinderRules.under_body 2 hf B)
  have hz2 := HornBinderRules.zf_body 2 hZ B
  have hmem := fiber_total hz2 false R (old 2 w) (old 2 A) (old 2 f) (slot 2 1) hw2 hf2 (.conjR (.conjR hB))
  have hord := fiber_total hz2 true R (old 2 w) (old 2 A) (old 2 f) (slot 2 1) hw2 hf2 (.conjR (.conjR hB))
  have ho : Derives Δ (boundGuards R (old 2 w) (old 2 A) (old 2 f)) := by
    apply HornBinderRules.intro_many 2 _ (slot 2)
    have hd : Derives Δ (B.conj ((fiber false R (old 2 w) (old 2 A) (old 2 f) (slot 2 1)).conj
      (fiber true R (old 2 w) (old 2 A) (old 2 f) (slot 2 1)))) := .conjI hB (.conjI hmem hord)
    exact of_eq (by simp only [B, Formula.rename, SyntaxMixedImageHead.head_rename, fiber_rename, assign_old, assign_slot]) hd
  exact of_eq (boundGuards_rename R w A f (old 2)).symm ho

/-- All ingredients for the original negative branch: actual child rebinding
and both guards at the new bound condition, without supplying any code output. -/
def negativeInputs {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) : Formula m :=
  (ForcingConditionRebind.fiber w a f A j N).conj (boundGuards R w A f)

theorem negative_inputs_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hN : Derives Γ (FormulaCodeSyntax.formulaCode w N a f)) : Derives Γ (negativeInputs R w a A f j N) :=
  .conjI (ForcingConditionRebind.fiber_total hZ w a f A j N hw hs hN)
    (bound_guards_total hZ R w a A f hw (.conjL (.conjR (FormulaCodeProperties.guards w N a f hN))) hs hf)

def negativeInputsSentence {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A a).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp
    ((FormulaCodeSyntax.formulaCode w N a f).imp (negativeInputs R w a A f j N))))).close

theorem negative_inputs_kernel_certificate {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (negativeInputsSentence R w a A f j N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact negative_inputs_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _)
    R w a A f j N (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingGuardCode


namespace PPAC.Migration.ForcingGuardCode
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature

/-- Readout of the EXISTING roles map, not a new variable substitution. -/
private theorem roles_variables (n : Nat) (i : Fin (n+3)) :
    roles n (fo_bound_variable i) =
      Fin.lastCases (.bvar .here) (fun j => .fvar (fo_bound_variable j)) i := by
  induction n with
  | zero =>
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (.fvar .here : PureSyntaxQuotation.Tm (fo_bound_context 1) (fo_bound_context (n+3))) =
        Fin.lastCases (.bvar .here) (fun j => .fvar (fo_bound_variable j)) (0 : Fin (n+3)).castSucc
      rw [Fin.lastCases_castSucc]
      rfl
    · change (roles n (fo_bound_variable j)).weakenFree SetSort.set = _
      rw [ih j]
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [Fin.lastCases_last]
        change (.bvar .here : PureSyntaxQuotation.Tm (fo_bound_context 1) (fo_bound_context (n+2))).weakenFree SetSort.set =
          Fin.lastCases (.bvar .here) (fun j => .fvar (fo_bound_variable j)) (Fin.last (n+3))
        rw [Fin.lastCases_last]
        rfl
      · rw [Fin.lastCases_castSucc]
        change (.fvar (fo_bound_variable k) : PureSyntaxQuotation.Tm (fo_bound_context 1) (fo_bound_context (n+2))).weakenFree SetSort.set =
          Fin.lastCases (.bvar .here) (fun j => .fvar (fo_bound_variable j)) k.succ.castSucc
        rw [Fin.lastCases_castSucc]
        rfl

/-- Exact source-language view of the original guard AST. Reuses the
completed Syntax.old_formula/substitute bridge for ALL source constructors. -/
theorem template_source {n} (order : Bool) (R : Source.Formula (n+2)) :
    template order R = Syntax.formula
      (Fin.lastCases (.bvar .here) (fun j => .fvar (fo_bound_variable j))) (sourceTemplate order R) := by
  unfold template
  rw [← Syntax.old_formula, Syntax.substitute]
  congr 1
  funext i
  exact roles_variables n i

/-- The literal R(q,p) guard, with original free parameters and p-slot.
Only AST metadata are identified here; object queries use the existing
NativeFormulaQuotationCorrespondence theorem. -/
theorem relation_template {n} (R : Source.Formula (n+2)) :
    template true R = Syntax.formula
      (Fin.lastCases (.fvar (fo_bound_variable (Fin.last (n+1))))
        (Fin.lastCases (.bvar .here) (fun i => .fvar (fo_bound_variable i.castSucc.castSucc)))) R := by
  rw [template_source]
  change Syntax.formula _ (ReplacementPredicates.rel R (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last (n+2)) (Fin.last (n+1)).castSucc) = _
  unfold ReplacementPredicates.rel Source.SetLanguage.relation
  rw [Syntax.rename]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.ForcingGuardCode
