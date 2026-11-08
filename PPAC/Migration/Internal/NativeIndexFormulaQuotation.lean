import PPAC.Migration.Internal.IndexImageQuotation
import PPAC.Migration.Internal.IndexFormulaRenameBridge

/-! Consume the EXISTING all-internal index/mixed-substitution bridge and
native quotation. Both converted environments are built inside object exists;
no correct mixed environment or output is supplied as a premise. -/
namespace PPAC.Migration.Internal.NativeIndexFormulaQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf)
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J a b c d n q r s : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I))
    (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J))
    (hp : ∀ j : Fin sb.length, Derives Γ (SchemaIndexQuotation.value j.val
      (ρ (NativeTopQuotationIndices.entryAt sb j)).index r))
    (hq : ∀ j : Fin sf.length, Derives Γ (SchemaIndexQuotation.value j.val
      (τ (NativeTopQuotationIndices.entryAt sf j)).index s))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).iff
      (PureQuotationSyntax.formula (input.substituteMapped (fun entry => .bvar (ρ entry)) (fun entry => .fvar (τ entry))) w q)) := by
  have he := IndexTermImageEnvironment.exists_environment hZ w I J a b c d hw
    (SyntaxMapCodeSyntax.intro_code w r a c I hr) (SyntaxMapCodeSyntax.intro_code w s b d J hs)
  let B := IndexTermImageCodeSyntax.environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb B)
  have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc B)
  have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd B)
  have hr2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc I.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hr B)
  have hs2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc J.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hs B)
  have hp2 (j : Fin sb.length) : Derives Δ (SchemaIndexQuotation.value j.val
      (ρ (NativeTopQuotationIndices.entryAt sb j)).index r.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SchemaIndexQuotation.value_rename]) (SyntaxRenameBinders.under_2 (hp j) B)
  have hq2 (j : Fin sf.length) : Derives Δ (SchemaIndexQuotation.value j.val
      (τ (NativeTopQuotationIndices.entryAt sf j)).index s.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SchemaIndexQuotation.value_rename]) (SyntaxRenameBinders.under_2 (hq j) B)
  have hn2 : Derives Δ (PureQuotationSyntax.formula input w.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,PureQuotationSyntax.formula_rename]) (SyntaxRenameBinders.under_2 hn B)
  have hE := IndexImageQuotation.renaming_environment hZ2 ρ τ _ _ _ _ _ _ _ _ _ _ _ hw2 ha2 hb2 hB hr2 hs2 hp2 hq2
  have hR := IndexFormulaRenameBridge.rename_iff hZ2 w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 hB
  have hN := NativeFormulaQuotationCorrespondence.formula_iff hZ2 input
    (fun entry => .bvar (ρ entry)) (fun entry => .fvar (τ entry)) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 ha2 hb2 hc2 hd2 hE hn2
  have ho := SyntaxTypeLocalTransfer.iff_trans hR hN
  exact of_eq (by simp only [Formula.raise,Formula.iff,Formula.rename,
    SyntaxRenameJudgmentSyntax.renamed_rename,PureQuotationSyntax.formula_rename]) ho

/-- Finite original source positions form a proof-scheme premise. The clauses
quantify candidate index/value codes in the OBJECT language. -/
def points {m} : (k : Nat) → (Fin k → Nat) → Fin m → Source.Formula m
  | 0, _, r => .equal r r
  | k+1, targets, r => (points k (fun j => targets j.castSucc) r).conj
      (SchemaIndexQuotation.value k (targets (Fin.last k)) r)

theorem points_at {m k} {Γ : Context m} (targets : Fin k → Nat) (r : Fin m)
    (h : Derives Γ (points k targets r)) (j : Fin k) :
    Derives Γ (SchemaIndexQuotation.value j.val (targets j) r) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact .conjR h
    · exact ih (fun i => targets i.castSucc) (.conjL h) i

theorem points_rename {m l} (k : Nat) (targets : Fin k → Nat) (r : Fin m) (ρ : Fin m → Fin l) :
    (points k targets r).rename ρ = points k targets (ρ r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [points,Formula.rename,ih,SchemaIndexQuotation.value_rename]

theorem points_intro {m k} {Γ : Context m} (targets : Fin k → Nat) (r : Fin m)
    (h : ∀ j : Fin k, Derives Γ (SchemaIndexQuotation.value j.val (targets j) r)) :
    Derives Γ (points k targets r) := by
  induction k with
  | zero => exact .eqRefl r
  | succ k ih => exact .conjI (ih (fun j => targets j.castSucc) (fun j => h j.castSucc)) (h (Fin.last k))

private def assumptions {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf)
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J a b c d n r s : Fin m) : Source.Formula m :=
  (omega w).conj
    (((SyntaxNumeralSyntax.numeral sb.length a).conj ((SyntaxNumeralSyntax.numeral sf.length b).conj
      ((SyntaxNumeralSyntax.numeral tb.length c).conj (SyntaxNumeralSyntax.numeral tf.length d)))).conj
      (((SyntaxMapCodeSyntax.encoded w r a c I).conj (SyntaxMapCodeSyntax.encoded w s b d J)).conj
        (((points sb.length (fun j => (ρ (NativeTopQuotationIndices.entryAt sb j)).index) r).conj
          (points sf.length (fun j => (τ (NativeTopQuotationIndices.entryAt sf j)).index) s)).conj
          (PureQuotationSyntax.formula input w n))))

def sentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf)
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J a b c d n q r s : Fin m) : Source.Sentence :=
  ((assumptions input ρ τ w I J a b c d n r s).imp
    ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).iff
      (PureQuotationSyntax.formula (input.substituteMapped (fun entry => .bvar (ρ entry)) (fun entry => .fvar (τ entry))) w q))).close

theorem source_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf)
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J a b c d n q r s : Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence input ρ τ w I J a b c d n q r s) := by
  apply close_derives
  apply Derives.impI
  let F := assumptions input ρ τ w I J a b c d n r s
  let Δ := Context.add F (Source.SetLanguage.ZF.at m)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hZ := ZFContext.add (ZFContext.source_ZF m) F
  have hL := Derives.conjL (.conjR hF)
  have hG := Derives.conjL (.conjR (.conjR hF))
  have hRest := Derives.conjR (.conjR (.conjR hF))
  have hPoints := Derives.conjL hRest
  exact formula_iff hZ input ρ τ w I J a b c d n q r s (.conjL hF)
    (.conjL hL) (.conjL (.conjR hL)) (.conjL (.conjR (.conjR hL))) (.conjR (.conjR (.conjR hL)))
    (.conjL hG) (.conjR hG) (points_at _ r (.conjL hPoints)) (points_at _ s (.conjR hPoints)) (.conjR hRest)

/-- Ordinary original nativeZF endpoint. Syntax and native maps remain external
scheme indices; all candidate code values are universally closed object variables. -/
theorem kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf)
    (ρ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sb sort → YesMetaZFC.Logic.FirstOrder.Variable tb sort)
    (τ : ∀ {sort}, YesMetaZFC.Logic.FirstOrder.Variable sf sort → YesMetaZFC.Logic.FirstOrder.Variable tf sort)
    (w I J a b c d n q r s : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence input ρ τ w I J a b c d n q r s)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate input ρ τ w I J a b c d n q r s))

end PPAC.Migration.Internal.NativeIndexFormulaQuotation
