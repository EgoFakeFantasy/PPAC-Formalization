import PPAC.Migration.ForcingConjunctionMono
import PPAC.Migration.ForcingCodeTotal
import PPAC.Migration.ForcingCodeUnary
import PPAC.Migration.ForcingRawModalBody

/-! Source-code induction interfaces for pinned force_mono.
The induction hypotheses quantify actual compiler outputs IN the object
theory. The conjunction step produces both child compilations with the
existing total compiler before invoking the accepted paired-query branch.
The constants discharge their source hypotheses. The negative and existential
constructors consume the same global runtime and produce the actual child
compilation. Atomic cases and the full induction remain open. -/
namespace PPAC.Migration.ForcingSourceMono
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open ForcingConjunctionMono (transfer transfer_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Every actual compilation of the source code has paired-query Root
transport in the specified runtime frame. This is an induction PROPERTY;
its cases use the corresponding source runtime frames. -/
def atSource {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a b G : Fin m) (R S : Fin 2 → Fin m) (n : Fin m) : Formula m := .all
  ((ForcingCodeRecursion.compiled Reln Dom w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)).imp
    (transfer test w.castSucc z.castSucc a.castSucc f.castSucc b.castSucc G.castSucc
      (fun i => (R i).castSucc) (fun i => (S i).castSucc) (Fin.last m)))
theorem atSource_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a b G : Fin m) (R S : Fin 2 → Fin m) (n : Fin m) (ρ : Fin m → Fin l) :
    (atSource test Reln Dom w z f j a b G R S n).rename ρ =
      atSource test Reln Dom (ρ w) (ρ z) (ρ f) (ρ j) (ρ a) (ρ b) (ρ G)
        (fun i => ρ (R i)) (fun i => ρ (S i)) (ρ n) := by
  simp only [atSource, Formula.rename, ForcingCodeRecursion.compiled_rename, transfer_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem apply_atSource {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a b G : Fin m) (R S : Fin 2 → Fin m) (n c : Fin m)
    (hi : Derives Γ (atSource test Reln Dom w z f j a b G R S n))
    (hc : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n c)) :
    Derives Γ (transfer test w z a f b G R S c) := by
  have h : Derives Γ ((ForcingCodeRecursion.compiled Reln Dom w z f j a n c).imp
    (transfer test w z a f b G R S c)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, ForcingCodeRecursion.compiled_rename,
      transfer_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE c hi)
  exact .impE h hc

private theorem nullary_transfer {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (truth : Bool) (w z a f b G n : Fin m) (R S : Fin 2 → Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (transfer test w z a f b G R S n) := by
  apply OriginalUniversalBlock.intro_many 2
  apply Derives.impI
  apply Derives.impI
  let B := (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 (R 0)) (old 2 (S 0))
    (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 0)).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 (R 1)) (old 2 (S 1))
        (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 1))
  let E := implication test (old 2 w) (old 2 z) (old 2 b) (old 2 G) (slot 2 0)
  let Δ := Context.add E (Context.add B (raisedContext 2 Γ))
  have hB : Derives Δ B := .hyp (Or.inr (Or.inl rfl))
  have hw2 : Derives Δ (omega (old 2 w)) := add
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)) E
  have hc2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) (old 2 w) Fin.elim0 (old 2 n)) :=
    add (of_eq (SyntaxNodeSyntax.constructor_rename 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n (old 2))
      (HornBinderRules.under_body 2 hc B)) E
  have hZ2 := ZFContext.add (HornBinderRules.zf_body 2 hZ B) E
  have ep := SyntaxMixedFormulaNullary.unique hZ2 truth (old 2 w) (old 2 (R 0)) (old 2 (S 0))
    (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 0) hw2 hc2 (.conjL hB)
  have eq := SyntaxMixedFormulaNullary.unique hZ2 truth (old 2 w) (old 2 (R 1)) (old 2 (S 1))
    (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 1) hw2 hc2 (.conjR hB)
  let P := implication test (old 2 w).castSucc (old 2 z).castSucc (old 2 b).castSucc (old 2 G).castSucc (Fin.last (m+2))
  exact of_eq (by simp only [P, Formula.instantiate, implication_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P (eq_trans ep (eq_symm eq))
      (of_eq (by simp only [P, Formula.instantiate, implication_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (Derives.hyp (Γ := Δ) (Or.inl rfl))))

/-- The actual compiler's constant law discharges the source base case.
No source IH, expected code equality, query answer or G proof is supplied. -/
theorem nullary {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (truth : Bool)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n : Fin m) (R S : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (formulaCode w n a z)) (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (atSource test Reln Dom w z f j a b G R S n) := by
  have ht := nullary_transfer hZ test truth w z a f b G n R S hw hc
  apply Derives.allI
  apply Derives.impI
  let E := ForcingCodeRecursion.compiled Reln Dom w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have he := ForcingCodeUnary.nullary (ZFContext.under hZ E) truth Reln Dom
    w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc n.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (SourceLogic.under hw E))
    (of_eq (formulaCode_rename w n a z Fin.castSucc) (SourceLogic.under hn E))
    (of_eq (successor_rename A a Fin.castSucc) (SourceLogic.under hA E))
    (of_eq (successor_rename B A Fin.castSucc) (SourceLogic.under hB E))
    (of_eq (successor_rename C B Fin.castSucc) (SourceLogic.under hC E))
    (of_eq (SyntaxNodeSyntax.constructor_rename 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n Fin.castSucc) (SourceLogic.under hc E))
    (Derives.hyp (Γ := Δ) (Or.inl rfl))
  let P := transfer test w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc
    b.castSucc.castSucc G.castSucc.castSucc (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) (Fin.last (m+1))
  exact of_eq (by simp only [P, Formula.instantiate, transfer_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P (eq_symm he) (of_eq
      (by simp only [P, Formula.instantiate, transfer_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (of_eq (transfer_rename test w z a f b G R S n Fin.castSucc) (SourceLogic.under ht E))))

private structure Frame (m : Nat) where
  w : Fin m
  z : Fin m
  f : Fin m
  j : Fin m
  a : Fin m
  A : Fin m
  B : Fin m
  C : Fin m
  b : Fin m
  G : Fin m
  n : Fin m
  x : Fin m
  y : Fin m
  R : Fin 2 → Fin m
  S : Fin 2 → Fin m
private def Frame.map {m l} (p : Frame m) (ρ : Fin m → Fin l) : Frame l :=
  ⟨ρ p.w,ρ p.z,ρ p.f,ρ p.j,ρ p.a,ρ p.A,ρ p.B,ρ p.C,ρ p.b,ρ p.G,ρ p.n,ρ p.x,ρ p.y,
    (fun i => ρ (p.R i)),(fun i => ρ (p.S i))⟩
private structure Inputs {k m} (Γ : Context m) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (p : Frame m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega p.w)
  empty : Derives Γ (empty p.z)
  f_num : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) p.f)
  j_num : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) p.j)
  scope1 : Derives Γ (successor p.A p.a)
  scope2 : Derives Γ (successor p.B p.A)
  scope3 : Derives Γ (successor p.C p.B)
  background : Derives Γ (formulaCode p.w p.G p.z p.b)
  parent : Derives Γ (formulaCode p.w p.n p.a p.z)
  ctor : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 p.w p.x p.y p.n)
  left : Derives Γ (atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.x)
  right : Derives Γ (atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.y)
private theorem Inputs.under {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {Dom : Source.Formula (k+1)} {p : Frame m}
    (h : Inputs Γ test Reln Dom p) (E : Formula (m+1)) :
    Inputs (Context.add E (Context.image Formula.raise Γ)) test Reln Dom (p.map Fin.castSucc) :=
  ⟨ZFContext.under h.zf E,
    of_eq (omega_rename p.w Fin.castSucc) (SourceLogic.under h.omega E),
    of_eq (empty_rename p.z Fin.castSucc) (SourceLogic.under h.empty E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) p.f Fin.castSucc) (SourceLogic.under h.f_num E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) p.j Fin.castSucc) (SourceLogic.under h.j_num E),
    of_eq (successor_rename p.A p.a Fin.castSucc) (SourceLogic.under h.scope1 E),
    of_eq (successor_rename p.B p.A Fin.castSucc) (SourceLogic.under h.scope2 E),
    of_eq (successor_rename p.C p.B Fin.castSucc) (SourceLogic.under h.scope3 E),
    of_eq (formulaCode_rename p.w p.G p.z p.b Fin.castSucc) (SourceLogic.under h.background E),
    of_eq (formulaCode_rename p.w p.n p.a p.z Fin.castSucc) (SourceLogic.under h.parent E),
    of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 p.w p.x p.y p.n Fin.castSucc) (SourceLogic.under h.ctor E),
    of_eq (atSource_rename test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.x Fin.castSucc) (SourceLogic.under h.left E),
    of_eq (atSource_rename test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.y Fin.castSucc) (SourceLogic.under h.right E)⟩

private theorem at_children {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {Dom : Source.Formula (k+1)} {p : Frame m}
    (h : Inputs Γ test Reln Dom p) (cx cy : Fin m)
    (hx : Derives Γ (ForcingCodeRecursion.compiled Reln Dom p.w p.z p.f p.j p.a p.x cx))
    (hy : Derives Γ (ForcingCodeRecursion.compiled Reln Dom p.w p.z p.f p.j p.a p.y cy)) :
    Derives Γ (atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.n) := by
  have tx := apply_atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.x cx h.left hx
  have ty := apply_atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.y cy h.right hy
  apply Derives.allI
  apply Derives.impI
  let E := ForcingCodeRecursion.compiled Reln Dom p.w.castSucc p.z.castSucc p.f.castSucc p.j.castSucc p.a.castSucc p.n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have h1 := h.under E
  have input : Derives Δ (ForcingCodeBinary.input 0 Reln Dom p.w.castSucc p.z.castSucc p.f.castSucc p.j.castSucc
    p.a.castSucc p.A.castSucc p.B.castSucc p.C.castSucc p.n.castSucc (Fin.last m) p.x.castSucc p.y.castSucc cx.castSucc cy.castSucc) :=
    .conjI h1.omega (.conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ h1.parent))
      (.conjI h1.scope1 (.conjI h1.scope2 (.conjI h1.scope3 (.conjI h1.ctor
        (.conjI (.hyp (Or.inl rfl))
          (.conjI (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom p.w p.z p.f p.j p.a p.x cx Fin.castSucc) (SourceLogic.under hx E))
            (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom p.w p.z p.f p.j p.a p.y cy Fin.castSucc) (SourceLogic.under hy E)))))))))
  exact ForcingConjunctionMono.source_step h1.zf test Reln Dom p.w.castSucc p.z.castSucc p.f.castSucc p.j.castSucc
    p.a.castSucc p.A.castSucc p.B.castSucc p.C.castSucc p.n.castSucc (Fin.last m) p.x.castSucc p.y.castSucc cx.castSucc cy.castSucc
    p.b.castSucc p.G.castSucc (fun i => (p.R i).castSucc) (fun i => (p.S i).castSucc)
    h1.empty h1.background input
    (of_eq (transfer_rename test p.w p.z p.a p.f p.b p.G p.R p.S cx Fin.castSucc) (SourceLogic.under tx E))
    (of_eq (transfer_rename test p.w p.z p.a p.f p.b p.G p.R p.S cy Fin.castSucc) (SourceLogic.under ty E))

-- Keep named object predicates opaque while matching the finite frame.
-- Expanding their proof-checker bodies is irrelevant to these binder steps.
attribute [local irreducible] atSource ForcingCodeRecursion.compiled

private theorem after_left {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {Dom : Source.Formula (k+1)} {p : Frame m}
    (h : Inputs Γ test Reln Dom p) (cx : Fin m)
    (hx : Derives Γ (ForcingCodeRecursion.compiled Reln Dom p.w p.z p.f p.j p.a p.x cx)) :
    Derives Γ (atSource test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.n) := by
  have types := Derives.impE (.conjL (FormulaCodeKnownLogical.binary0_iff h.zf p.w p.a p.z p.x p.y p.n h.omega h.ctor)) h.parent
  have he := ForcingCodeTotal.total h.zf Reln Dom p.w p.z p.f p.j p.a p.y h.omega h.empty h.f_num h.j_num (.conjR (.conjR types))
  let E := ForcingCodeRecursion.compiled Reln Dom p.w.castSucc p.z.castSucc p.f.castSucc p.j.castSucc p.a.castSucc p.y.castSucc (Fin.last m)
  apply Derives.exE (p := E) he
  have out := at_children (p := p.map Fin.castSucc) (Γ := Context.add E (Context.image Formula.raise Γ))
    (h.under E) cx.castSucc (Fin.last m)
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom p.w p.z p.f p.j p.a p.x cx Fin.castSucc) (SourceLogic.under hx E))
    (Derives.hyp (Γ := Context.add E (Context.image Formula.raise Γ)) (Or.inl rfl))
  exact of_eq (atSource_rename test Reln Dom p.w p.z p.f p.j p.a p.b p.G p.R p.S p.n Fin.castSucc).symm out

def conjunctionInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n x y : Fin m) (R S : Fin 2 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj
    ((successor A a).conj ((successor B A).conj ((successor C B).conj ((formulaCode w G z b).conj
      ((formulaCode w n a z).conj ((SyntaxLogicalSyntax.binaryCode 0 w x y n).conj
        ((atSource test Reln Dom w z f j a b G R S x).conj (atSource test Reln Dom w z f j a b G R S y)))))))))))
theorem conjunctionInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n x y : Fin m) (R S : Fin 2 → Fin m) (ρ : Fin m → Fin l) :
    (conjunctionInput test Reln Dom w z f j a A B C b G n x y R S).rename ρ =
      conjunctionInput test Reln Dom (ρ w) (ρ z) (ρ f) (ρ j) (ρ a) (ρ A) (ρ B) (ρ C) (ρ b) (ρ G) (ρ n) (ρ x) (ρ y)
        (fun i => ρ (R i)) (fun i => ρ (S i)) := by
  simp only [conjunctionInput, Formula.rename, omega_rename, empty_rename, SyntaxNumeralSyntax.numeral_rename,
    successor_rename, formulaCode_rename, SyntaxLogicalSyntax.binaryCode_rename, atSource_rename]

/-- Actual SOURCE induction step: generate both compiler outputs internally,
instantiate both source IHs, and invoke the original paired-query branch. -/
theorem conjunction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n x y : Fin m) (R S : Fin 2 → Fin m)
    (hi : Derives Γ (conjunctionInput test Reln Dom w z f j a A B C b G n x y R S)) :
    Derives Γ (atSource test Reln Dom w z f j a b G R S n) := by
  let p : Frame m := ⟨w,z,f,j,a,A,B,C,b,G,n,x,y,R,S⟩
  have h : Inputs Γ test Reln Dom p := ⟨hZ,
    .conjL hi, .conjL (.conjR hi), .conjL (.conjR (.conjR hi)), .conjL (.conjR (.conjR (.conjR hi))),
    .conjL (.conjR (.conjR (.conjR (.conjR hi)))), .conjL (.conjR (.conjR (.conjR (.conjR (.conjR hi))))),
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi)))))),
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))),
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi)))))))),
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))))),
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi)))))))))),
    .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))))))⟩
  have types := Derives.impE (.conjL (FormulaCodeKnownLogical.binary0_iff h.zf w a z x y n h.omega h.ctor)) h.parent
  have he := ForcingCodeTotal.total h.zf Reln Dom w z f j a x h.omega h.empty h.f_num h.j_num (.conjL (.conjR types))
  let E := ForcingCodeRecursion.compiled Reln Dom w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc x.castSucc (Fin.last m)
  apply Derives.exE (p := E) he
  have out := after_left (p := p.map Fin.castSucc) (Γ := Context.add E (Context.image Formula.raise Γ))
    (h.under E) (Fin.last m) (Derives.hyp (Γ := Context.add E (Context.image Formula.raise Γ)) (Or.inl rfl))
  exact of_eq (atSource_rename test Reln Dom w z f j a b G R S n Fin.castSucc).symm out

def conjunctionSentence {k m} (target : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n x y : Fin m) (R S : Fin 2 → Fin m) : Source.Sentence :=
  ((conjunctionInput (OriginalAxiomCodeTest.test target) Reln Dom w z f j a A B C b G n x y R S).imp
    (atSource (OriginalAxiomCodeTest.test target) Reln Dom w z f j a b G R S n)).close
theorem conjunction_kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n x y : Fin m) (R S : Fin 2 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (conjunctionSentence target Reln Dom w z f j a A B C b G n x y R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact conjunction (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target)
    Reln Dom w z f j a A B C b G n x y R S (.hyp (Or.inl rfl))

def nullarySentence {k m} (target truth : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n : Fin m) (R S : Fin 2 → Fin m) : Source.Sentence :=
  (((omega w).conj ((formulaCode w n a z).conj ((successor A a).conj ((successor B A).conj ((successor C B).conj
    (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)))))).imp
      (atSource (OriginalAxiomCodeTest.test target) Reln Dom w z f j a b G R S n)).close
theorem nullary_kernel_certificate {k m} (target truth : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C b G n : Fin m) (R S : Fin 2 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (nullarySentence target truth Reln Dom w z f j a A B C b G n R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact nullary (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target) truth
    Reln Dom w z f j a A B C b G n R S
    (.conjL (.hyp (Or.inl rfl))) (.conjL (.conjR (.hyp (Or.inl rfl))))
    (.conjL (.conjR (.conjR (.hyp (Or.inl rfl))))) (.conjL (.conjR (.conjR (.conjR (.hyp (Or.inl rfl))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.hyp (Or.inl rfl)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.hyp (Or.inl rfl)))))))


/-- The two modal source constructors use their actual branch compiler and
the same global runtime as the compiled-parent transfer. -/
def modalInput {k m} (existential : Bool) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha beta gamma n xCode : Fin m) : Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x
      oldCtx).conj
    ((formulaCode w n a z).conj ((successor alpha a).conj ((successor beta alpha).conj
      ((successor gamma beta).conj (SyntaxLogicalSyntax.singleCode (if existential then 10 else 4) w xCode n)))))

set_option maxHeartbeats 1600000 in
theorem modal {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (existential : Bool) (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha beta gamma n xCode : Fin m)
    (hi : Derives Γ (modalInput existential test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx alpha beta
      gamma n xCode)) :
    Derives Γ (atSource test Reln Dom w z f j a b (oldCtx 3) (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n) := by
  have runtime := Derives.conjL hi
  have rest := Derives.conjR hi
  have parent := Derives.conjL rest
  have rest := Derives.conjR rest
  have hAlpha := Derives.conjL rest
  have rest := Derives.conjR rest
  have hBeta := Derives.conjL rest
  have rest := Derives.conjR rest
  have hGamma := Derives.conjL rest
  have ctor := Derives.conjR rest
  have global := Derives.conjL runtime
  have fresh := Derives.conjL (.conjR global)
  have images := Derives.conjL (.conjR (.conjR (.conjL fresh)))
  have hw := Derives.conjL (.conjL images)
  have hz := Derives.conjL (.conjL fresh)
  have members := Derives.conjL (.conjL (.conjL global))
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR members))))
  have hj := Derives.conjL (.conjR (.conjR runtime))
  let aChild := if existential then alpha else a
  have child : Derives Γ (formulaCode w xCode aChild z) := by
    cases existential
    · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.negation_iff hZ w a z xCode n hw ctor)) parent)
    · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.quantified_iff hZ false w a z xCode n alpha hw ctor hAlpha)) parent)
  have total := ForcingCodeTotal.typed_total hZ Reln Dom w z f j aChild xCode hw hz hf hj child
  let E := (ForcingCodeRecursion.compiled Reln Dom (old 1 w) (old 1 z) (old 1 f) (old 1 j) (old 1 aChild)
    (old 1 xCode) (slot 1 0)).conj (formulaCode (old 1 w) (slot 1 0) (old 1 aChild) (old 1 f))
  let Δ := Context.add E (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 E _ total
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  apply of_eq (by simp only [atSource_rename, SyntaxAtomSyntax.two_map]; rfl)
  unfold atSource
  apply Derives.allI
  apply Derives.impI
  let G := ForcingCodeRecursion.compiled Reln Dom (old 1 (old 1 w)) (old 1 (old 1 z)) (old 1 (old 1 f))
    (old 1 (old 1 j)) (old 1 (old 1 a)) (old 1 (old 1 n)) (slot 1 0)
  let Ξ := Context.add G (raisedContext 1 Δ)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  let rho := fun i : Fin m => old 1 (old 1 i)
  let N := old 1 (slot (m := m) 1 0)
  let Q : Fin ((m+1)+1) := slot 1 0
  have move {p : Formula m} (hp : Derives Γ p) : Derives Ξ (p.rename rho) :=
    of_eq (rename_comp p (old 1) (old 1))
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hp E) G)
  have runtime' := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K
      Extra raw v C Refl Pre U0 P x oldCtx rho) (move runtime)
  have hw' := of_eq (omega_rename w rho) (move hw)
  have hn' := of_eq (by rfl : (Formula.mem n w).rename rho = Formula.mem (rho n) (rho w))
    (move (.conjL (FormulaCodeProperties.guards w n a z parent)))
  have alpha' := of_eq (successor_rename alpha a rho) (move hAlpha)
  have beta' := of_eq (successor_rename beta alpha rho) (move hBeta)
  have gamma' := of_eq (successor_rename gamma beta rho) (move hGamma)
  have ctor' := of_eq (SyntaxLogicalSyntax.singleCode_rename (if existential then 10 else 4) w xCode n rho) (move ctor)
  have childCompiler := of_eq (ForcingCodeRecursion.compiled_rename Reln Dom (old 1 w) (old 1 z) (old 1 f)
    (old 1 j) (old 1 aChild) (old 1 xCode) (slot 1 0) (old 1)) (HornBinderRules.under_body 1 (.conjL hE) G)
  have childType := of_eq (formulaCode_rename (old 1 w) (slot 1 0) (old 1 aChild) (old 1 f) (old 1))
    (HornBinderRules.under_body 1 (.conjR hE) G)
  have zf := HornBinderRules.zf_body 1 (HornBinderRules.zf_body 1 hZ E) G
  let kind : Fin 3 := if existential then 2 else 0
  have branch := ForcingCodeUnary.unary zf kind Reln Dom (rho w) (rho z) (rho f) (rho j) (rho a)
    (rho alpha) (rho beta) (rho gamma) (rho n) Q (rho xCode) N hw' hn' alpha' beta' gamma'
    (by cases existential <;> exact ctor') hG (by cases existential <;> exact childCompiler)
  cases existential
  · exact ForcingRawModalBody.transfer_negative_global zf test Reln (rho w) (rho z) (rho a) (rho f) (rho j) (rho b) (rho B)
      (rho R) (rho S) (rho T) (rho SOld) (rho SNew) (rho A1) (rho A2) (rho A3) (rho K) (rho Extra) (fun i => rho (raw i))
      (fun i => rho (v i)) (fun i => rho (C i)) (fun i => rho (Refl i)) (fun i => rho (Pre i)) (fun i => rho (U0 i))
      (fun s i => rho (P s i)) (fun i => rho (x i)) (fun i => rho (oldCtx i))
      (rho alpha) N Q (.conjI runtime' (.conjI alpha' (.conjI childType branch)))
  · exact ForcingRawModalBody.transfer_existential_global zf test Reln Dom (rho w) (rho z) (rho a) (rho f) (rho j) (rho b)
      (rho B) (rho R) (rho S) (rho T) (rho SOld) (rho SNew) (rho A1) (rho A2) (rho A3) (rho K) (rho Extra)
      (fun i => rho (raw i)) (fun i => rho (v i)) (fun i => rho (C i)) (fun i => rho (Refl i)) (fun i => rho (Pre i))
      (fun i => rho (U0 i)) (fun s i => rho (P s i)) (fun i => rho (x i)) (fun i => rho (oldCtx i))
      (rho alpha) (rho beta) (rho gamma) N Q
      (.conjI runtime' (.conjI alpha' (.conjI beta' (.conjI gamma' (.conjI childType branch)))))

theorem modal_kernel_certificate {k m} (existential : Bool) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha beta gamma n xCode : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence ((modalInput existential test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx alpha beta
      gamma n xCode).imp
        (atSource test Reln Dom w z f j a b (oldCtx 3) (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact modal (ZFContext.add (ZFContext.source_ZF m) _) existential test Reln Dom w z a f j b B R S T SOld SNew A1 A2 A3 K
      Extra raw v C Refl Pre U0 P x oldCtx alpha beta gamma n xCode (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingSourceMono
