import PPAC.Migration.ForcingAtomicRelations
import PPAC.Migration.Internal.PureQuotationTypedFormulas
import PPAC.Migration.Internal.TypedArgumentListConstruction
import PPAC.Migration.Internal.FreeSubstImageCode
import PPAC.Migration.Internal.ProofTreeEntryFacts

/-! Literal migrated atomic-forcing code: internal construction, not a Con proof.
The input atom terms are arbitrary internal codes in a closed source context.
Target bound scope is internal; only the fixed ground-language template is a
host AST. All actual image lists are constructed by the existing internal syntax interfaces. -/
namespace PPAC.Migration.ForcingAtomicCode
section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature

private def roles : (n : Nat) → VariableSubstitution ℒ
    (fo_bound_context (n+4)) (fo_bound_context 2) (fo_bound_context (n+2))
  | 0 => fun v => match v with
    | .here => .fvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .bvar (.there .here)
    | .there (.there (.there .here)) => .bvar .here
    | .there (.there (.there (.there v))) => nomatch v
  | n+1 => fun v => match v with
    | .here => .fvar .here
    | .there v => by
      simpa only [fo_bound_context, List.replicate_succ] using (roles n v).weakenFree SetSort.set

def sourceTemplate {n} (equality : Bool) (R : Source.Formula (n+2)) : Source.Formula (n+4) :=
  ForcingAtomicRelations.forces equality R
    (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3))
    (Fin.last (n+1)).castSucc.castSucc

/-- Bounds 0/1 are y/x; free variables are the original R parameters, P, p.
This is a typed substitution in the LITERAL existing forcing formula. -/
def template {n} (equality : Bool) (R : Source.Formula (n+2)) :
    PureSyntaxQuotation.Fm (fo_bound_context 2) (fo_bound_context (n+2)) :=
  (Translation.formula fo_bound_variable (sourceTemplate equality R)).substituteMapped
    (roles n) (fun {sort} (v : FirstOrder.Variable ([] : FirstOrder.SortContext ℒ) sort) => nomatch v)

end Templates

open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

private theorem closed_term_target {m} {Γ : Context m} (w a z b x : Fin m)
    (hz : Derives Γ (empty z)) (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x)) :
    Derives Γ (SyntaxTermSyntax.term w a b x) := by
  apply Derives.conjI hc
  apply Derives.disjE (.conjR hx)
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := SyntaxTermSyntax.branch false w z x
    let B := SyntaxTermSyntax.branchWitness false w z x
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under (add hz P) B)
    exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.conjL (.hyp (Or.inl rfl))))

private theorem forest_typed {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w size a b L : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k size))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (ht : ∀ i, Derives Γ (SyntaxTermSyntax.term w a b (xs i)))
    (hf : Derives Γ (SyntaxForestSyntax.forest k w xs L)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w size a b L) := by
  induction k generalizing m with
  | zero => exact TypedArgumentListConstruction.nil_list hZ w size a b L hw hn hc hf
  | succ k ih =>
    let P := (SyntaxNumeralSyntax.numeral k (Fin.last m)).conj (successor size.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ k size _ hn
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hf1 := of_eq (SyntaxForestSyntax.forest_rename (k+1) w xs L Fin.castSucc) (under hf P)
    let B := (Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
      ((SyntaxForestSyntax.forest k w.castSucc.castSucc
        (fun i => (xs i.succ).castSucc.castSucc) (Fin.last (m+1))).conj
        (StructuralListSyntax.consCode w.castSucc.castSucc (xs 0).castSucc.castSucc
          (Fin.last (m+1)) L.castSucc.castSucc))
    let Ξ := Context.add B (Context.image Formula.raise Δ)
    apply SyntaxForestSyntax.eliminate_cons k w.castSucc (fun i => (xs i).castSucc) L.castSucc _ hf1
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have lift2 {Q : Formula m} (h : Derives Γ Q) : Derives Ξ Q.raise.raise := under (under h P) B
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (lift2 hw)
    have hc2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc
        a.castSucc.castSucc b.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (lift2 hc)
    have ht2 (i : Fin (k+1)) : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc
        a.castSucc.castSucc b.castSucc.castSucc (xs i).castSucc.castSucc) := of_eq
      (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 (ht i))
    have hn2 := of_eq (SyntaxNumeralSyntax.numeral_rename k (Fin.last m) Fin.castSucc) (under (.conjL hP) B)
    have hs2 := of_eq (successor_rename size.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hP) B)
    have htail := ih (ZFContext.under (ZFContext.under hZ P) B) w.castSucc.castSucc
      (Fin.last m).castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
      (fun i => (xs i.succ).castSucc.castSucc) hw2 hn2 hc2 (fun i => ht2 i.succ) (.conjL (.conjR hB))
    have hout := TypedArgumentListConstruction.cons_list (ZFContext.under (ZFContext.under hZ P) B)
      w.castSucc.castSucc (Fin.last m).castSucc size.castSucc.castSucc
      a.castSucc.castSucc b.castSucc.castSucc (xs 0).castSucc.castSucc
      (Fin.last (m+1)) L.castSucc.castSucc hw2 (ht2 0) htail (.conjR (.conjR hB)) hs2
    exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) hout

private def freeImages {m} (w a f S : Fin m) : Formula m := .ex
  ((SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc))

private theorem freeImages_rename {m l} (w a f S : Fin m) (r : Fin m → Fin l) :
    (freeImages w a f S).rename r = freeImages (r w) (r a) (r f) (r S) := by
  simp only [freeImages, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename,
    IndexTermImageCodeSyntax.converted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private def existsFreeImages {m} (w a f : Fin m) : Formula m := .ex
  (freeImages w.castSucc a.castSucc f.castSucc (Fin.last m))

private theorem existsFreeImages_rename {m l} (w a f : Fin m) (r : Fin m → Fin l) :
    (existsFreeImages w a f).rename r = existsFreeImages (r w) (r a) (r f) := by
  simp only [existsFreeImages, Formula.rename, freeImages_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem freeImages_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (existsFreeImages w a f) := by
  let B := SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxIdentityCode.exists_code hZ w f hw hf)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hctx : Derives Δ (SyntaxTermSyntax.contexts w.castSucc a.castSucc f.castSucc) :=
    .conjI (under ha B) (under hf B)
  have hm := SyntaxIdentityCode.map_code w.castSucc f.castSucc (Fin.last m) hB
  have he := IndexTermImageCodeExistence.exists_code (ZFContext.under hZ B) false
    w.castSucc (Fin.last m) f.castSucc a.castSucc f.castSucc hw1 (.conjI hctx hm)
  let C := IndexTermImageCodeSyntax.converted false w.castSucc.castSucc (Fin.last m).castSucc
    (Fin.last (m+1)) f.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) he
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hi2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc f.castSucc
    (Fin.last m) Fin.castSucc) (under hB C)
  have hfree : Derives Ξ (freeImages w.castSucc.castSucc a.castSucc.castSucc
      f.castSucc.castSucc (Fin.last (m+1))) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [C, Formula.instantiate, Formula.rename,
      SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.converted_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hi2 hC)
  have hout : Derives Ξ (existsFreeImages w.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, freeImages_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hfree
  exact of_eq (by simp only [Formula.raise, existsFreeImages_rename]) hout

private theorem freeImages_typed {m} {Γ : Context m} (w a f S : Fin m)
    (h : Derives Γ (freeImages w a f S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w f a f S) := by
  let B := (SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc)
  apply Derives.exE (p := B) h
  have hB : Derives (Context.add B (Context.image Formula.raise Γ)) B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f a f S Fin.castSucc).symm
    (IndexTermImageCodeTyping.term_list false w.castSucc (Fin.last m) S.castSucc
      f.castSucc a.castSucc f.castSucc (.conjR hB))

private def matrix {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 2 (v 0)).conj
    ((SyntaxNumeralSyntax.numeral (n+2) (v 1)).conj
      ((PureQuotationTypedSyntax.formulaValue (template equality R) w (v 0) (v 1) (v 2)).conj
        ((SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) (v 3)).conj
          ((SyntaxMixedImageCodeSyntax.termList w (v 0) a (v 1) (v 3)).conj
            ((freeImages w a (v 1) (v 4)).conj
              (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 3) (v 4) (v 0) (v 1) a (v 1) (v 2) q))))))

private theorem matrix_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (v : Fin 5 → Fin m) (r : Fin m → Fin l) :
    (matrix equality R w a x y q v).rename r =
      matrix equality R (r w) (r a) (r x) (r y) (r q) (fun i => r (v i)) := by
  simp only [matrix, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    PureQuotationTypedSyntax.formulaValue, PureQuotationSyntax.formula_rename,
    FormulaCodeSyntax.formulaCode_rename, SyntaxForestSyntax.forest_rename,
    ProofTreeEntryFacts.args2_map, SyntaxMixedImageCodeSyntax.termList_rename,
    freeImages_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private def body {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) : Formula (m+5) :=
  matrix equality R (old 5 w) (old 5 a) (old 5 x) (old 5 y) (old 5 q) (slot 5)

def compiled {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) : Formula m := existsMany 5 (body equality R w a x y q)

private theorem compiled_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (r : Fin m → Fin l) :
    (compiled equality R w a x y q).rename r = compiled equality R (r w) (r a) (r x) (r y) (r q) := by
  simp only [compiled, existsMany_rename, body, matrix_rename, lift_old, lift_slot]

def existsCompiled {n m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y : Fin m) : Formula m := .ex
  (compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m))

private theorem existsCompiled_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y : Fin m) (r : Fin m → Fin l) :
    (existsCompiled equality R w a x y).rename r = existsCompiled equality R (r w) (r a) (r x) (r y) := by
  simp only [existsCompiled, Formula.rename, compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs (n m : Nat) (Γ : Context m) (w t f a x y : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hx : Derives Γ (SyntaxTermSyntax.term w a f x)
  hy : Derives Γ (SyntaxTermSyntax.term w a f y)

private theorem underInputs {n m} {Γ : Context m} {w t f a x y : Fin m}
    (h : Inputs n m Γ w t f a x y) (B : Formula (m+1)) :
    Inputs n (m+1) (Context.add B (Context.image Formula.raise Γ))
      w.castSucc t.castSucc f.castSucc a.castSucc x.castSucc y.castSucc := by
  exact {
  hw := of_eq (omega_rename w Fin.castSucc) (under h.hw B)
  ht := of_eq (SyntaxNumeralSyntax.numeral_rename 2 t Fin.castSucc) (under h.ht B)
  hf := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf B)
  hx := of_eq (SyntaxTermSyntax.term_rename w a f x Fin.castSucc) (under h.hx B)
  hy := of_eq (SyntaxTermSyntax.term_rename w a f y Fin.castSucc) (under h.hy B) }

private theorem quotation_rename {n m l} (equality : Bool) (R : Source.Formula (n+2))
    (w t f N : Fin m) (r : Fin m → Fin l) :
    (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N).rename r =
      PureQuotationTypedSyntax.formulaValue (template equality R) (r w) (r t) (r f) (r N) := by
  simp only [PureQuotationTypedSyntax.formulaValue, Formula.rename,
    PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

private theorem assemble {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N U V : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U))
    (hV : Derives Γ (freeImages w a f V)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w U V t f a f N) :=
    .conjI (.conjR hN) (.conjI htU (freeImages_typed w a f V hV))
  let B := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc U.castSucc V.castSucc
    t.castSucc f.castSucc a.castSucc f.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B)
    (SyntaxMixedFormulaOutputInduction.actual_exists hZ w U V t f a f N h.hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hU1 := of_eq (by simpa only [ProofTreeEntryFacts.args2_map] using
    SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) U Fin.castSucc) (under hU B)
  have htU1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)
  have hV1 := of_eq (freeImages_rename w a f V Fin.castSucc) (under hV B)
  let v : Fin 5 → Fin (m+1) := Fin.cases t.castSucc (Fin.cases f.castSucc
    (Fin.cases N.castSucc (SetLanguage.args2 U.castSucc V.castSucc)))
  have hm : Derives Δ (matrix equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m) v) :=
    .conjI h1.ht (.conjI h1.hf (.conjI hN1 (.conjI hU1 (.conjI htU1 (.conjI hV1 hB)))))
  have hc : Derives Δ (compiled equality R w.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 5 _ v
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  have ho : Derives Δ (existsCompiled equality R w.castSucc a.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_free_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N U : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N))
    (hU : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) U))
    (htU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w t a f U)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  let B := freeImages w.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B)
    (freeImages_exists hZ w a f h.hw (.conjL (.conjL h.hx)) (.conjR (.conjL h.hx)))
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hU1 := of_eq (by simpa only [ProofTreeEntryFacts.args2_map] using
    SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) U Fin.castSucc) (under hU B)
  have htU1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w t a f U Fin.castSucc) (under htU B)
  have ho := assemble (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc N.castSucc U.castSucc (Fin.last m)
    h1 hN1 hU1 htU1 (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_bound_images {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y N : Fin m)
    (h : Inputs n m Γ w t f a x y)
    (hN : Derives Γ (PureQuotationTypedSyntax.formulaValue (template equality R) w t f N)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have hn : ∀ i, Derives Γ (.mem (SetLanguage.args2 y x i) w) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact SyntaxTerms.range hZ w a f y h.hw h.hy
    · refine Fin.cases ?_ (fun v => Fin.elim0 v) j
      exact SyntaxTerms.range hZ w a f x h.hw h.hx
  have he := SyntaxForests.exists_forest hZ 2 w (SetLanguage.args2 y x) h.hw
    (SyntaxForestSyntax.intro_inputs 2 w (SetLanguage.args2 y x) hn)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxForestSyntax.forest 2 w.castSucc (SetLanguage.args2 y.castSucc x.castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (of_eq (by
    simp only [B, SyntaxForestSyntax.existsForest, ProofTreeEntryFacts.args2_map]) he)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h1 := underInputs h B
  have hN1 := of_eq (quotation_rename equality R w t f N Fin.castSucc) (under hN B)
  have hterms : ∀ i, Derives Δ (SyntaxTermSyntax.term w.castSucc a.castSucc f.castSucc
      (SetLanguage.args2 y.castSucc x.castSucc i)) := by
    intro i
    refine Fin.cases h1.hy (fun j => ?_) i
    exact Fin.cases h1.hx (fun v => Fin.elim0 v) j
  have htU := forest_typed (ZFContext.under hZ B) w.castSucc t.castSucc a.castSucc f.castSucc
    (Fin.last m) (SetLanguage.args2 y.castSucc x.castSucc)
    h1.hw h1.ht (.conjL h1.hx) hterms (.conjR hB)
  have ho := with_free_images (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc N.castSucc (Fin.last m) h1 hN1 (.conjR hB) htU
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

private theorem with_template {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w t f a x y : Fin m)
    (h : Inputs n m Γ w t f a x y) :
    Derives Γ (existsCompiled equality R w a x y) := by
  have ht : Derives Γ (SyntaxNumeralSyntax.numeral
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 2).length t) := by
    have he : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 2).length = 2 := by
      exact List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k t)) he) h.ht
  have hf : Derives Γ (SyntaxNumeralSyntax.numeral
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) := by
    have he : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 := by
      exact List.length_replicate ..
    exact Eq.mpr (congrArg (fun k => Derives Γ (SyntaxNumeralSyntax.numeral k f)) he) h.hf
  have he := PureQuotationTypedFormulas.exists_typed hZ (template equality R) w t f h.hw ht hf
  let B := PureQuotationTypedSyntax.formulaValue (template equality R)
    w.castSucc t.castSucc f.castSucc (Fin.last m)
  apply Derives.exE (p := B) he
  have ho := with_bound_images (ZFContext.under hZ B) equality R w.castSucc t.castSucc f.castSucc
    a.castSucc x.castSucc y.castSucc (Fin.last m) (underInputs h B) (.hyp (Or.inl rfl))
  exact of_eq (existsCompiled_rename equality R w a x y Fin.castSucc).symm ho

/-- Construct every quotation, scope numeral, and substitution image internally.
The input terms have zero free variables; their bound scope may be nonstandard. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x))
    (hy : Derives Γ (SyntaxTermSyntax.term w a z y)) :
    Derives Γ (existsCompiled equality R w a x y) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxNumeralSyntax.numeral (n+2) (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (SyntaxNumerals.exists_numeral (ZFContext.under hZ B) (n+2) w.castSucc hw1)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have lift2 {Q : Formula m} (h : Derives Γ Q) : Derives Ξ Q.raise.raise := under (under h B) C
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (lift2 hw)
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, empty_rename]) (lift2 hz)
  have hx2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 hx)
  have hy2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (lift2 hy)
  have hc : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))) :=
    .conjI (.conjL (.conjL hx2)) (.conjL hC)
  have ht2 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 (Fin.last m) Fin.castSucc) (under (.conjR hB) C)
  have h : Inputs n (m+2) Ξ w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      a.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc :=
    ⟨hw2, ht2, .conjR hC, closed_term_target _ _ _ _ _ hz2 hc hx2, closed_term_target _ _ _ _ _ hz2 hc hy2⟩
  have ho := with_template (ZFContext.under (ZFContext.under hZ B) C) equality R
    w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc
    x.castSucc.castSucc y.castSucc.castSucc h
  exact of_eq (by simp only [Formula.raise, existsCompiled_rename]) ho

def typed {m} (n : Nat) (w a q : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral (n+2) (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc q.castSucc a.castSucc (Fin.last m)))

private theorem typed_rename {m l} (n : Nat) (w a q : Fin m) (r : Fin m → Fin l) :
    (typed n w a q).rename r = typed n (r w) (r a) (r q) := by
  simp only [typed, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    FormulaCodeSyntax.formulaCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Every actual compiler output has the exact target bound/free scope. -/
theorem compiled_type {n m} {Γ : Context m} (equality : Bool) (R : Source.Formula (n+2))
    (w a x y q : Fin m) (h : Derives Γ (compiled equality R w a x y q)) :
    Derives Γ (typed n w a q) := by
  let B := body equality R w a x y q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B (typed n w a q) h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf := Derives.conjL (.conjR hB)
  have hQ := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have ht := SyntaxMixedFormulaJudgment.target_type (old 5 w) (slot 5 3) (slot 5 4)
    (slot 5 0) (slot 5 1) (old 5 a) (slot 5 1) (slot 5 2) (old 5 q) hQ
  have ho : Derives Δ (typed n (old 5 w) (old 5 a) (old 5 q)) := by
    apply Derives.exI (slot 5 1)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxNumeralSyntax.numeral_rename, FormulaCodeSyntax.formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hf ht)
  exact of_eq (typed_rename n w a q (old 5)).symm ho

def sentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxTermSyntax.term w a z x).imp
    ((SyntaxTermSyntax.term w a z y).imp (existsCompiled equality R w a x y))))).close

def typeSentence {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m) : Source.Sentence :=
  ((compiled equality R w a x y q).imp (typed n w a q)).close

theorem kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a z x y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence equality R w a z x y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _)
    equality R w a z x y (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem type_kernel_certificate {n m} (equality : Bool) (R : Source.Formula (n+2)) (w a x y q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (typeSentence equality R w a x y q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact compiled_type equality R w a x y q (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingAtomicCode
