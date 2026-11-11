import PPAC.Migration.ForcingFreshOpeningInverse
import PPAC.Migration.ForcingWeakenedImages
import PPAC.Migration.ForcingMixedUnary
import PPAC.Migration.Internal.StructuralConsCore
import PPAC.Migration.ForcingNegCode
import PPAC.Migration.ForcingExistCode

/-! Open the actual queried universal or existential parent, with its original complete
mixed tables. Generate both lifted tables, both bodies, the weakened parent,
the native fresh instance, and the direct raw-body query. No expected body,
map equality, instance answer or external-standardness premise is supplied.
The remaining source guard/tail consumer must identify the generated raw
body with the SAME nested proof body; this file does not assume that match. -/
namespace PPAC.Migration.ForcingFreshParentOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def quantifiedInput {m} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor alpha a).conj
    ((successor A z).conj ((successor B b).conj
      ((SyntaxVariableSyntax.code false w z t).conj
        ((SyntaxTermSyntax.term w z B t).conj
          ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).conj
            (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z b n Parent))))))))

theorem quantifiedInput_rename {m l} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) (rho : Fin m → Fin l) :
    (quantifiedInput universal w z a f alpha b A B t R S n x Parent).rename rho =
      quantifiedInput universal (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) := by
  simp only [quantifiedInput, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxTermSyntax.term_rename,
    SyntaxLogicalSyntax.singleCode_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

/-- Nine retained outputs: old/new lifted bound/free tables, original and
weakened target bodies, weakened whole parent, prefixed raw bound table,
and its actual raw body output. The separate native output is eliminated
by the EXISTING generic binder formula theorem. -/
def quantifiedData {m} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Formula m :=
  (quantifiedInput universal w z a f alpha b A B t R S n x Parent).conj
    ((ForcingWeakenedImages.data w a f z b B R S v).conj
      ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z b alpha A (u 0) (u 1)).conj
        ((SyntaxCodedMixedBinderSyntax.lifted w (v 8) (v 9) a f z B alpha A (u 2) (u 3)).conj
          ((SyntaxMixedFormulaJudgmentSyntax.substituted w (u 0) (u 1) alpha f A b x (u 4)).conj
            ((SyntaxMixedFormulaJudgmentSyntax.substituted w (u 2) (u 3) alpha f A B x (u 5)).conj
              ((SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) (v 9) a f z B n (u 6)).conj
                ((StructuralListSyntax.consCode w t (v 8) (u 7)).conj
                  ((SyntaxMixedFormulaJudgmentSyntax.substituted w (u 7) (v 9) alpha f z B x (u 8)).conj
                    ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w (u 4) Parent).conj
                      ((ForcingFreshOpeningInverse.input w z b A B t (u 4) (u 5) (u 8)).conj
                        (SyntaxTopFormulaSyntax.abstracted w z b A B (u 8) (u 4))))))))))))

theorem quantifiedData_rename {m l} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (rho : Fin m → Fin l) :
    (quantifiedData universal w z a f alpha b A B t R S n x Parent v u).rename rho =
      quantifiedData universal (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent)
        (fun i => rho (v i)) (fun i => rho (u i)) := by
  simp only [quantifiedData, Formula.rename, quantifiedInput_rename, ForcingWeakenedImages.data_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename,
    StructuralListSyntax.consCode_rename, SyntaxLogicalSyntax.singleCode_rename,
    ForcingFreshOpeningInverse.input_rename, SyntaxTopFormulaSyntax.abstracted_rename]

def quantifiedAtImages {m} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 9 (quantifiedData universal (old 9 w) (old 9 z) (old 9 a) (old 9 f) (old 9 alpha) (old 9 b) (old 9 A) (old 9 B)
    (old 9 t) (old 9 R) (old 9 S) (old 9 n) (old 9 x) (old 9 Parent) (fun i => old 9 (v i)) (slot 9))

theorem quantifiedAtImages_rename {m l} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m)
    (v : Fin 10 → Fin m) (rho : Fin m → Fin l) :
    (quantifiedAtImages universal w z a f alpha b A B t R S n x Parent v).rename rho =
      quantifiedAtImages universal (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) := by
  simp only [quantifiedAtImages, existsMany_rename, quantifiedData_rename, lift_old, lift_slot]

private def quantifiedBody {m} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) : Formula (m+10) :=
  quantifiedAtImages universal (old 10 w) (old 10 z) (old 10 a) (old 10 f) (old 10 alpha) (old 10 b) (old 10 A) (old 10 B)
    (old 10 t) (old 10 R) (old 10 S) (old 10 n) (old 10 x) (old 10 Parent) (slot 10)

def quantifiedProduced {m} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) : Formula m :=
  existsMany 10 (quantifiedBody universal w z a f alpha b A B t R S n x Parent)

theorem quantifiedProduced_rename {m l} (universal : Bool) (w z a f alpha b A B t R S n x Parent : Fin m) (rho : Fin m → Fin l) :
    (quantifiedProduced universal w z a f alpha b A B t R S n x Parent).rename rho =
      quantifiedProduced universal (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) := by
  simp only [quantifiedProduced, existsMany_rename, quantifiedBody, quantifiedAtImages_rename, lift_old, lift_slot]

private structure Params (m : Nat) where
  universal : Bool
  w : Fin m
  z : Fin m
  a : Fin m
  f : Fin m
  alpha : Fin m
  b : Fin m
  A : Fin m
  B : Fin m
  t : Fin m
  R : Fin m
  S : Fin m
  n : Fin m
  x : Fin m
  Parent : Fin m

private def Params.map {m l} (p : Params m) (rho : Fin m → Fin l) : Params l :=
  ⟨p.universal,rho p.w,rho p.z,rho p.a,rho p.f,rho p.alpha,rho p.b,rho p.A,rho p.B,
    rho p.t,rho p.R,rho p.S,rho p.n,rho p.x,rho p.Parent⟩

private structure Inputs {m} (Gamma : Context m) (p : Params m) (v : Fin 10 → Fin m) : Prop where
  zf : ZFContext.Evidence Gamma
  source : Derives Gamma (quantifiedInput p.universal p.w p.z p.a p.f p.alpha p.b p.A p.B p.t p.R p.S p.n p.x p.Parent)
  images : Derives Gamma (ForcingWeakenedImages.data p.w p.a p.f p.z p.b p.B p.R p.S v)

private theorem Inputs.in_body {m l} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Gamma)) (p.map (old l)) (fun i => old l (v i)) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (quantifiedInput_rename p.universal p.w p.z p.a p.f p.alpha p.b p.A p.B p.t p.R p.S p.n p.x p.Parent (old l))
      (HornBinderRules.under_body l h.source E),
    of_eq (ForcingWeakenedImages.data_rename p.w p.a p.f p.z p.b p.B p.R p.S v (old l))
      (HornBinderRules.under_body l h.images E)⟩

private theorem Inputs.hw {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (omega p.w) := .conjL h.source
private theorem Inputs.hz {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (empty p.z) := .conjL (.conjR h.source)
private theorem Inputs.hAlpha {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (successor p.alpha p.a) := .conjL (.conjR (.conjR h.source))
private theorem Inputs.hA {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (successor p.A p.z) := .conjL (.conjR (.conjR (.conjR h.source)))
private theorem Inputs.hB {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (successor p.B p.b) := .conjL (.conjR (.conjR (.conjR (.conjR h.source))))
private theorem Inputs.fresh {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxVariableSyntax.code false p.w p.z p.t) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.source)))))
private theorem Inputs.term {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxTermSyntax.term p.w p.z p.B p.t) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.source))))))
private theorem Inputs.ctor {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag p.universal) p.w p.x p.n) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.source)))))))
private theorem Inputs.query {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted
      p.w p.R p.S p.a p.f p.z p.b p.n p.Parent) :=
  .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.source)))))))
private theorem Inputs.old_input {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxMixedFormulaOutputSyntax.input p.w p.R p.S p.a p.f p.z p.b p.n) :=
  SyntaxMixedFormulaOutput.input_of_substituted h.zf p.w p.R p.S p.a p.f p.z p.b p.n p.Parent h.hw h.query
private theorem Inputs.child_type {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (FormulaCodeSyntax.formulaCode p.w p.x p.alpha p.f) :=
  .conjR (.impE (.conjL (FormulaCodeKnownLogical.quantified_iff h.zf p.universal p.w p.a p.f p.x p.n p.alpha
    h.hw h.ctor h.hAlpha)) (.conjL h.old_input))
private theorem Inputs.new_lists {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) : Derives Gamma (SyntaxMixedImageCodeSyntax.termLists p.w p.a p.f p.z p.B (v 8) (v 9)) :=
  SyntaxMixedImageCodePairs.term_lists p.w (v 6) (v 7) p.a p.f p.z p.B (v 8) (v 9)
    (.conjR (.conjR (.conjR (.conjR h.images))))

private theorem at_outputs {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) (K H L M F U W V D Y : Fin m)
    (hl0 : Derives Gamma (SyntaxCodedMixedBinderSyntax.lifted p.w p.R p.S p.a p.f p.z p.b p.alpha p.A K H))
    (hl1 : Derives Gamma (SyntaxCodedMixedBinderSyntax.lifted p.w (v 8) (v 9) p.a p.f p.z p.B p.alpha p.A L M))
    (hF : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted p.w K H p.alpha p.f p.A p.b p.x F))
    (hU : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted p.w L M p.alpha p.f p.A p.B p.x U))
    (hW : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted p.w (v 8) (v 9) p.a p.f p.z p.B p.n W))
    (hV : Derives Gamma (SyntaxTopFormulaSyntax.instantiated p.w p.z p.B p.A p.t U V))
    (hD : Derives Gamma (StructuralListSyntax.consCode p.w p.t (v 8) D))
    (hY : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted p.w D (v 9) p.alpha p.f p.z p.B p.x Y)) :
    Derives Gamma (quantifiedData p.universal p.w p.z p.a p.f p.alpha p.b p.A p.B p.t p.R p.S p.n p.x p.Parent v
      (Fin.cases K (Fin.cases H (Fin.cases L (Fin.cases M (Fin.cases F
        (Fin.cases U (Fin.cases W (SyntaxAtomSyntax.two D Y))))))))) := by
  have oldCtor := ForcingMixedUnary.quantified_constructor h.zf p.universal p.w p.R p.S p.a p.f p.z p.b p.n p.x p.Parent F
    p.alpha p.A K H h.hw h.old_input h.ctor h.query hl0 hF
  have newInput : Derives Gamma (SyntaxMixedFormulaOutputSyntax.input p.w (v 8) (v 9) p.a p.f p.z p.B p.n) :=
    .conjI (.conjL h.old_input) h.new_lists
  have newCtor := ForcingMixedUnary.quantified_constructor h.zf p.universal p.w (v 8) (v 9) p.a p.f p.z p.B p.n p.x W U
    p.alpha p.A L M h.hw newInput h.ctor hW hl1 hU
  have wholeWeak := ForcingWeakenedImages.from_queries h.zf p.w p.a p.f p.z p.b p.B p.R p.S p.n p.Parent W v
    (.conjI h.images (.conjI h.query hW))
  have targetType := SyntaxMixedFormulaJudgment.target_type p.w p.R p.S p.a p.f p.z p.b p.n p.Parent h.query
  have scopes := FormulaCodeProperties.guards p.w p.Parent p.z p.b targetType
  have bodyWeak := Derives.impE (.conjL (SyntaxWeakenFreeLogicalInternal.quantified_iff h.zf p.universal
    p.w p.z p.b p.B p.Parent W F U p.A h.hw (.conjL (.conjR scopes)) (.conjR (.conjR scopes))
    h.hB h.hA oldCtor newCtor)) wholeWeak
  have eq := ForcingBinderFormula.native h.zf p.w p.z p.a p.f p.B p.alpha p.A (v 8) (v 9) L M p.t D p.x U V Y
    h.hw h.hz h.new_lists hl1 hD hU hV hY
  let E := SyntaxTopFormulaSyntax.instantiated p.w.castSucc p.z.castSucc p.B.castSucc p.A.castSucc
    p.t.castSucc U.castSucc (Fin.last m)
  have inst : Derives Gamma (SyntaxTopFormulaSyntax.instantiated p.w p.z p.B p.A p.t U Y) :=
    of_eq (by simp only [E, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst E eq (of_eq (by simp only [E, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hV))
  have inverse : Derives Gamma (ForcingFreshOpeningInverse.input p.w p.z p.b p.A p.B p.t F U Y) :=
    .conjI h.hw (.conjI h.hz (.conjI h.hA (.conjI h.fresh (.conjI bodyWeak inst))))
  have abstract := ForcingFreshOpeningInverse.derive h.zf p.w p.z p.b p.A p.B p.t F U Y inverse
  exact .conjI h.source (.conjI h.images (.conjI hl0 (.conjI hl1 (.conjI hF (.conjI hU
    (.conjI hW (.conjI hD (.conjI hY (.conjI oldCtor (.conjI inverse abstract))))))))))


private theorem at_images {m} {Gamma : Context m} {p : Params m} {v : Fin 10 → Fin m}
    (h : Inputs Gamma p v) :
    Derives Gamma (quantifiedAtImages p.universal p.w p.z p.a p.f p.alpha p.b p.A p.B p.t p.R p.S p.n p.x p.Parent v) := by
  let E0 := SyntaxCodedMixedBinderSyntax.lifted (p.map (old 2)).w (p.map (old 2)).R (p.map (old 2)).S (p.map (old 2)).a (p.map (old 2)).f (p.map (old 2)).z
      (p.map (old 2)).b (p.map (old 2)).alpha (p.map (old 2)).A (slot 2 0) (slot 2 1)
  let Delta1 := Context.add E0 (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E0 _ (SyntaxCodedMixedBinderExistence.exists_pair h.zf p.w p.R p.S p.a p.f p.z p.b p.alpha p.A h.hw (.conjI (.conjR
      h.old_input) (.conjI h.hAlpha h.hA)))
  let p1 := p.map (old 2)
  let v1 : Fin 10 → Fin (m+2) := fun j => old 2 (v j)
  have h1 : Inputs Delta1 p1 v1 := h.in_body E0
  have hl0_1 : Derives Delta1 (SyntaxCodedMixedBinderSyntax.lifted p1.w p1.R p1.S p1.a p1.f p1.z p1.b p1.alpha p1.A (slot 2 0) (slot 2 1)) := .hyp (Or.inl rfl)
  let E1 := SyntaxCodedMixedBinderSyntax.lifted (p1.map (old 2)).w ((fun j => old 2 (v1 j)) 8) ((fun j => old 2 (v1 j)) 9) (p1.map (old 2)).a (p1.map (old 2)).f
      (p1.map (old 2)).z (p1.map (old 2)).B (p1.map (old 2)).alpha (p1.map (old 2)).A (slot 2 0) (slot 2 1)
  let Delta2 := Context.add E1 (raisedContext 2 Delta1)
  apply HornBinderRules.eliminate_many 2 E1 _ (SyntaxCodedMixedBinderExistence.exists_pair h1.zf p1.w (v1 8) (v1 9) p1.a p1.f p1.z p1.B p1.alpha p1.A h1.hw
      (.conjI h1.new_lists (.conjI h1.hAlpha h1.hA)))
  let p2 := p1.map (old 2)
  let v2 : Fin 10 → Fin ((m+2)+2) := fun j => old 2 (v1 j)
  have h2 : Inputs Delta2 p2 v2 := h1.in_body E1
  have hl0_2 : Derives Delta2 (SyntaxCodedMixedBinderSyntax.lifted p2.w p2.R p2.S p2.a p2.f p2.z p2.b p2.alpha p2.A (old 2 (slot 2 0)) (old 2 (slot 2 1))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 2 hl0_1 E1)
  have hl1_2 : Derives Delta2 (SyntaxCodedMixedBinderSyntax.lifted p2.w (v2 8) (v2 9) p2.a p2.f p2.z p2.B p2.alpha p2.A (slot 2 0) (slot 2 1)) := .hyp (Or.inl
      rfl)
  let E2 := SyntaxMixedFormulaJudgmentSyntax.substituted (p2.map (old 1)).w (old 1 (old 2 (slot 2 0))) (old 1 (old 2 (slot 2 1))) (p2.map (old 1)).alpha (p2.map
      (old 1)).f (p2.map (old 1)).A (p2.map (old 1)).b (p2.map (old 1)).x (slot 1 0)
  let Delta3 := Context.add E2 (raisedContext 1 Delta2)
  apply HornBinderRules.eliminate_many 1 E2 _ (SyntaxMixedFormulaOutputInduction.actual_exists h2.zf p2.w (old 2 (slot 2 0)) (old 2 (slot 2 1)) p2.alpha p2.f
      p2.A p2.b p2.x h2.hw
    (.conjI h2.child_type (SyntaxCodedMixedBinderTyping.output_lists p2.w p2.R p2.S p2.a p2.f p2.z p2.b p2.alpha p2.A (old 2 (slot 2 0)) (old 2 (slot 2 1))
        hl0_2)))
  let p3 := p2.map (old 1)
  let v3 : Fin 10 → Fin (((m+2)+2)+1) := fun j => old 1 (v2 j)
  have h3 : Inputs Delta3 p3 v3 := h2.in_body E2
  have hl0_3 : Derives Delta3 (SyntaxCodedMixedBinderSyntax.lifted p3.w p3.R p3.S p3.a p3.f p3.z p3.b p3.alpha p3.A (old 1 (old 2 (slot 2 0))) (old 1 (old 2
      (slot 2 1)))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_2 E2)
  have hl1_3 : Derives Delta3 (SyntaxCodedMixedBinderSyntax.lifted p3.w (v3 8) (v3 9) p3.a p3.f p3.z p3.B p3.alpha p3.A (old 1 (slot 2 0)) (old 1 (slot 2 1)))
      :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_2 E2)
  have hF_3 : Derives Delta3 (SyntaxMixedFormulaJudgmentSyntax.substituted p3.w (old 1 (old 2 (slot 2 0))) (old 1 (old 2 (slot 2 1))) p3.alpha p3.f p3.A p3.b
      p3.x (slot 1 0)) := .hyp (Or.inl rfl)
  let E3 := SyntaxMixedFormulaJudgmentSyntax.substituted (p3.map (old 1)).w (old 1 (old 1 (slot 2 0))) (old 1 (old 1 (slot 2 1))) (p3.map (old 1)).alpha (p3.map
      (old 1)).f (p3.map (old 1)).A (p3.map (old 1)).B (p3.map (old 1)).x (slot 1 0)
  let Delta4 := Context.add E3 (raisedContext 1 Delta3)
  apply HornBinderRules.eliminate_many 1 E3 _ (SyntaxMixedFormulaOutputInduction.actual_exists h3.zf p3.w (old 1 (slot 2 0)) (old 1 (slot 2 1)) p3.alpha p3.f
      p3.A p3.B p3.x h3.hw
    (.conjI h3.child_type (SyntaxCodedMixedBinderTyping.output_lists p3.w (v3 8) (v3 9) p3.a p3.f p3.z p3.B p3.alpha p3.A (old 1 (slot 2 0)) (old 1 (slot 2 1))
        hl1_3)))
  let p4 := p3.map (old 1)
  let v4 : Fin 10 → Fin ((((m+2)+2)+1)+1) := fun j => old 1 (v3 j)
  have h4 : Inputs Delta4 p4 v4 := h3.in_body E3
  have hl0_4 : Derives Delta4 (SyntaxCodedMixedBinderSyntax.lifted p4.w p4.R p4.S p4.a p4.f p4.z p4.b p4.alpha p4.A (old 1 (old 1 (old 2 (slot 2 0)))) (old 1
      (old 1 (old 2 (slot 2 1))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_3 E3)
  have hl1_4 : Derives Delta4 (SyntaxCodedMixedBinderSyntax.lifted p4.w (v4 8) (v4 9) p4.a p4.f p4.z p4.B p4.alpha p4.A (old 1 (old 1 (slot 2 0))) (old 1 (old 1
      (slot 2 1)))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_3 E3)
  have hF_4 : Derives Delta4 (SyntaxMixedFormulaJudgmentSyntax.substituted p4.w (old 1 (old 1 (old 2 (slot 2 0)))) (old 1 (old 1 (old 2 (slot 2 1)))) p4.alpha
      p4.f p4.A p4.b p4.x (old 1 (slot 1 0))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hF_3 E3)
  have hU_4 : Derives Delta4 (SyntaxMixedFormulaJudgmentSyntax.substituted p4.w (old 1 (old 1 (slot 2 0))) (old 1 (old 1 (slot 2 1))) p4.alpha p4.f p4.A p4.B
      p4.x (slot 1 0)) := .hyp (Or.inl rfl)
  let E4 := SyntaxMixedFormulaJudgmentSyntax.substituted (p4.map (old 1)).w ((fun j => old 1 (v4 j)) 8) ((fun j => old 1 (v4 j)) 9) (p4.map (old 1)).a (p4.map
      (old 1)).f (p4.map (old 1)).z (p4.map (old 1)).B (p4.map (old 1)).n (slot 1 0)
  let Delta5 := Context.add E4 (raisedContext 1 Delta4)
  apply HornBinderRules.eliminate_many 1 E4 _ (SyntaxMixedFormulaOutputInduction.actual_exists h4.zf p4.w (v4 8) (v4 9) p4.a p4.f p4.z p4.B p4.n h4.hw (.conjI
      (.conjL h4.old_input) h4.new_lists))
  let p5 := p4.map (old 1)
  let v5 : Fin 10 → Fin (((((m+2)+2)+1)+1)+1) := fun j => old 1 (v4 j)
  have h5 : Inputs Delta5 p5 v5 := h4.in_body E4
  have hl0_5 : Derives Delta5 (SyntaxCodedMixedBinderSyntax.lifted p5.w p5.R p5.S p5.a p5.f p5.z p5.b p5.alpha p5.A (old 1 (old 1 (old 1 (old 2 (slot 2 0)))))
      (old 1 (old 1 (old 1 (old 2 (slot 2 1)))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_4 E4)
  have hl1_5 : Derives Delta5 (SyntaxCodedMixedBinderSyntax.lifted p5.w (v5 8) (v5 9) p5.a p5.f p5.z p5.B p5.alpha p5.A (old 1 (old 1 (old 1 (slot 2 0)))) (old
      1 (old 1 (old 1 (slot 2 1))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_4 E4)
  have hF_5 : Derives Delta5 (SyntaxMixedFormulaJudgmentSyntax.substituted p5.w (old 1 (old 1 (old 1 (old 2 (slot 2 0))))) (old 1 (old 1 (old 1 (old 2 (slot 2
      1))))) p5.alpha p5.f p5.A p5.b p5.x (old 1 (old 1 (slot 1 0)))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hF_4 E4)
  have hU_5 : Derives Delta5 (SyntaxMixedFormulaJudgmentSyntax.substituted p5.w (old 1 (old 1 (old 1 (slot 2 0)))) (old 1 (old 1 (old 1 (slot 2 1)))) p5.alpha
      p5.f p5.A p5.B p5.x (old 1 (slot 1 0))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hU_4 E4)
  have hW_5 : Derives Delta5 (SyntaxMixedFormulaJudgmentSyntax.substituted p5.w (v5 8) (v5 9) p5.a p5.f p5.z p5.B p5.n (slot 1 0)) := .hyp (Or.inl rfl)
  let E5 := SyntaxTopFormulaSyntax.instantiated (p5.map (old 1)).w (p5.map (old 1)).z (p5.map (old 1)).B (p5.map (old 1)).A (p5.map (old 1)).t (old 1 (old 1
      (slot 1 0))) (slot 1 0)
  let Delta6 := Context.add E5 (raisedContext 1 Delta5)
  apply HornBinderRules.eliminate_many 1 E5 _ (SyntaxTopFormulaExistence.instantiate_exists h5.zf p5.w p5.z p5.B p5.A p5.t (old 1 (slot 1 0)) h5.hw
    (.conjI (.conjI h5.term h5.hA) (SyntaxMixedFormulaJudgment.target_type p5.w (old 1 (old 1 (old 1 (slot 2 0)))) (old 1 (old 1 (old 1 (slot 2 1)))) p5.alpha
        p5.f p5.A p5.B p5.x (old 1 (slot 1 0)) hU_5)))
  let p6 := p5.map (old 1)
  let v6 : Fin 10 → Fin ((((((m+2)+2)+1)+1)+1)+1) := fun j => old 1 (v5 j)
  have h6 : Inputs Delta6 p6 v6 := h5.in_body E5
  have hl0_6 : Derives Delta6 (SyntaxCodedMixedBinderSyntax.lifted p6.w p6.R p6.S p6.a p6.f p6.z p6.b p6.alpha p6.A (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2
      0)))))) (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 1))))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_5 E5)
  have hl1_6 : Derives Delta6 (SyntaxCodedMixedBinderSyntax.lifted p6.w (v6 8) (v6 9) p6.a p6.f p6.z p6.B p6.alpha p6.A (old 1 (old 1 (old 1 (old 1 (slot 2
      0))))) (old 1 (old 1 (old 1 (old 1 (slot 2 1)))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_5 E5)
  have hF_6 : Derives Delta6 (SyntaxMixedFormulaJudgmentSyntax.substituted p6.w (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 0)))))) (old 1 (old 1 (old 1 (old 1
      (old 2 (slot 2 1)))))) p6.alpha p6.f p6.A p6.b p6.x (old 1 (old 1 (old 1 (slot 1 0))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hF_5 E5)
  have hU_6 : Derives Delta6 (SyntaxMixedFormulaJudgmentSyntax.substituted p6.w (old 1 (old 1 (old 1 (old 1 (slot 2 0))))) (old 1 (old 1 (old 1 (old 1 (slot 2
      1))))) p6.alpha p6.f p6.A p6.B p6.x (old 1 (old 1 (slot 1 0)))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hU_5 E5)
  have hW_6 : Derives Delta6 (SyntaxMixedFormulaJudgmentSyntax.substituted p6.w (v6 8) (v6 9) p6.a p6.f p6.z p6.B p6.n (old 1 (slot 1 0))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hW_5 E5)
  have hV_6 : Derives Delta6 (SyntaxTopFormulaSyntax.instantiated p6.w p6.z p6.B p6.A p6.t (old 1 (old 1 (slot 1 0))) (slot 1 0)) := .hyp (Or.inl rfl)
  let E6 := (Formula.mem (slot 1 0) (old 1 p6.w)).conj (StructuralListSyntax.consCode (p6.map (old 1)).w (p6.map (old 1)).t ((fun j => old 1 (v6 j)) 8) (slot 1
      0))
  let Delta7 := Context.add E6 (raisedContext 1 Delta6)
  apply HornBinderRules.eliminate_many 1 E6 _ (StructuralConsCore.exists_cons h6.zf p6.w p6.t (v6 8) h6.hw (SyntaxTerms.range h6.zf p6.w p6.z p6.B p6.t h6.hw
      h6.term)
    (.conjL (.conjL (.conjR (.conjR (.conjL h6.new_lists))))))
  let p7 := p6.map (old 1)
  let v7 : Fin 10 → Fin (((((((m+2)+2)+1)+1)+1)+1)+1) := fun j => old 1 (v6 j)
  have h7 : Inputs Delta7 p7 v7 := h6.in_body E6
  have hl0_7 : Derives Delta7 (SyntaxCodedMixedBinderSyntax.lifted p7.w p7.R p7.S p7.a p7.f p7.z p7.b p7.alpha p7.A (old 1 (old 1 (old 1 (old 1 (old 1 (old 2
      (slot 2 0))))))) (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 1)))))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_6 E6)
  have hl1_7 : Derives Delta7 (SyntaxCodedMixedBinderSyntax.lifted p7.w (v7 8) (v7 9) p7.a p7.f p7.z p7.B p7.alpha p7.A (old 1 (old 1 (old 1 (old 1 (old 1 (slot
      2 0)))))) (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 1))))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_6 E6)
  have hF_7 : Derives Delta7 (SyntaxMixedFormulaJudgmentSyntax.substituted p7.w (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 0))))))) (old 1 (old 1 (old 1
      (old 1 (old 1 (old 2 (slot 2 1))))))) p7.alpha p7.f p7.A p7.b p7.x (old 1 (old 1 (old 1 (old 1 (slot 1 0)))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hF_6 E6)
  have hU_7 : Derives Delta7 (SyntaxMixedFormulaJudgmentSyntax.substituted p7.w (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 0)))))) (old 1 (old 1 (old 1 (old 1
      (old 1 (slot 2 1)))))) p7.alpha p7.f p7.A p7.B p7.x (old 1 (old 1 (old 1 (slot 1 0))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hU_6 E6)
  have hW_7 : Derives Delta7 (SyntaxMixedFormulaJudgmentSyntax.substituted p7.w (v7 8) (v7 9) p7.a p7.f p7.z p7.B p7.n (old 1 (old 1 (slot 1 0)))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hW_6 E6)
  have hV_7 : Derives Delta7 (SyntaxTopFormulaSyntax.instantiated p7.w p7.z p7.B p7.A p7.t (old 1 (old 1 (old 1 (slot 1 0)))) (old 1 (slot 1 0))) :=
    of_eq (by simp only [SyntaxTopFormulaSyntax.instantiated_rename]; rfl) (HornBinderRules.under_body 1 hV_6 E6)
  have hD_7 : Derives Delta7 (StructuralListSyntax.consCode p7.w p7.t (v7 8) (slot 1 0)) := .conjR (.hyp (Or.inl rfl))
  let E7 := SyntaxMixedFormulaJudgmentSyntax.substituted (p7.map (old 1)).w (old 1 (slot 1 0)) ((fun j => old 1 (v7 j)) 9) (p7.map (old 1)).alpha (p7.map (old
      1)).f (p7.map (old 1)).z (p7.map (old 1)).B (p7.map (old 1)).x (slot 1 0)
  let Delta8 := Context.add E7 (raisedContext 1 Delta7)
  apply HornBinderRules.eliminate_many 1 E7 _ (SyntaxMixedFormulaOutputInduction.actual_exists h7.zf p7.w (slot 1 0) (v7 9) p7.alpha p7.f p7.z p7.B p7.x h7.hw
    (.conjI h7.child_type (.conjI
      (TypedArgumentListConstruction.cons_list h7.zf p7.w p7.a p7.alpha p7.z p7.B p7.t (v7 8) (slot 1 0) h7.hw h7.term (.conjL h7.new_lists) hD_7 h7.hAlpha)
          (.conjR h7.new_lists))))
  let p8 := p7.map (old 1)
  let v8 : Fin 10 → Fin ((((((((m+2)+2)+1)+1)+1)+1)+1)+1) := fun j => old 1 (v7 j)
  have h8 : Inputs Delta8 p8 v8 := h7.in_body E7
  have hl0_8 : Derives Delta8 (SyntaxCodedMixedBinderSyntax.lifted p8.w p8.R p8.S p8.a p8.f p8.z p8.b p8.alpha p8.A (old 1 (old 1 (old 1 (old 1 (old 1 (old 1
      (old 2 (slot 2 0)))))))) (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 1))))))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl0_7 E7)
  have hl1_8 : Derives Delta8 (SyntaxCodedMixedBinderSyntax.lifted p8.w (v8 8) (v8 9) p8.a p8.f p8.z p8.B p8.alpha p8.A (old 1 (old 1 (old 1 (old 1 (old 1 (old
      1 (slot 2 0))))))) (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 1)))))))) :=
    of_eq (by simp only [SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (HornBinderRules.under_body 1 hl1_7 E7)
  have hF_8 : Derives Delta8 (SyntaxMixedFormulaJudgmentSyntax.substituted p8.w (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 0)))))))) (old 1 (old 1
      (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 1)))))))) p8.alpha p8.f p8.A p8.b p8.x (old 1 (old 1 (old 1 (old 1 (old 1 (slot 1 0))))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hF_7 E7)
  have hU_8 : Derives Delta8 (SyntaxMixedFormulaJudgmentSyntax.substituted p8.w (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 0))))))) (old 1 (old 1 (old 1
      (old 1 (old 1 (old 1 (slot 2 1))))))) p8.alpha p8.f p8.A p8.B p8.x (old 1 (old 1 (old 1 (old 1 (slot 1 0)))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hU_7 E7)
  have hW_8 : Derives Delta8 (SyntaxMixedFormulaJudgmentSyntax.substituted p8.w (v8 8) (v8 9) p8.a p8.f p8.z p8.B p8.n (old 1 (old 1 (old 1 (slot 1 0))))) :=
    of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 1 hW_7 E7)
  have hV_8 : Derives Delta8 (SyntaxTopFormulaSyntax.instantiated p8.w p8.z p8.B p8.A p8.t (old 1 (old 1 (old 1 (old 1 (slot 1 0))))) (old 1 (old 1 (slot 1
      0)))) :=
    of_eq (by simp only [SyntaxTopFormulaSyntax.instantiated_rename]; rfl) (HornBinderRules.under_body 1 hV_7 E7)
  have hD_8 : Derives Delta8 (StructuralListSyntax.consCode p8.w p8.t (v8 8) (old 1 (slot 1 0))) :=
    of_eq (by simp only [StructuralListSyntax.consCode_rename]; rfl) (HornBinderRules.under_body 1 hD_7 E7)
  have hY_8 : Derives Delta8 (SyntaxMixedFormulaJudgmentSyntax.substituted p8.w (old 1 (slot 1 0)) (v8 9) p8.alpha p8.f p8.z p8.B p8.x (slot 1 0)) := .hyp
      (Or.inl rfl)
  have hd := at_outputs h8 (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 0)))))))) (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 1))))))))
      (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 0))))))) (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 1))))))) (old 1 (old 1 (old 1 (old 1 (old 1
      (slot 1 0)))))) (old 1 (old 1 (old 1 (old 1 (slot 1 0))))) (old 1 (old 1 (old 1 (slot 1 0)))) (old 1 (old 1 (slot 1 0))) (old 1 (slot 1 0)) (slot 1 0)
    hl0_8 hl1_8 hF_8 hU_8 hW_8 hV_8 hD_8 hY_8
  have result : Derives Delta8 (quantifiedAtImages p8.universal p8.w p8.z p8.a p8.f p8.alpha p8.b p8.A p8.B p8.t p8.R p8.S p8.n p8.x p8.Parent v8) := by
    apply HornBinderRules.intro_many 9 _ (Fin.cases (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (old 2 (slot 2 0)))))))) (Fin.cases (old 1 (old 1 (old 1 (old 1
        (old 1 (old 1 (old 2 (slot 2 1)))))))) (Fin.cases (old 1 (old 1 (old 1 (old 1 (old 1 (old 1 (slot 2 0))))))) (Fin.cases (old 1 (old 1 (old 1 (old 1 (old
        1 (old 1 (slot 2 1))))))) (Fin.cases (old 1 (old 1 (old 1 (old 1 (old 1 (slot 1 0)))))) (Fin.cases (old 1 (old 1 (old 1 (old 1 (slot 1 0))))) (Fin.cases
        (old 1 (old 1 (old 1 (slot 1 0)))) (SyntaxAtomSyntax.two (old 1 (slot 1 0)) (slot 1 0)))))))))
    exact of_eq (by simp only [quantifiedData_rename, assign_old, assign_slot]) hd
  exact of_eq (by simp only [quantifiedAtImages_rename]; rfl) result

/-- Reuse the SAME actual weak-image record supplied by an existing source
producer, including WeakenedOverwrite. This is the unchanged private proof,
so canonical tables need not be regenerated or identified afterwards. -/
theorem produce_quantified_at_images {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (universal : Bool)
    (w z a f alpha b A B t R S n x Parent : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Gamma (quantifiedInput universal w z a f alpha b A B t R S n x Parent))
    (hv : Derives Gamma (ForcingWeakenedImages.data w a f z b B R S v)) :
    Derives Gamma (quantifiedAtImages universal w z a f alpha b A B t R S n x Parent v) :=
  at_images (Gamma := Gamma) (p := ⟨universal,w,z,a,f,alpha,b,A,B,t,R,S,n,x,Parent⟩) (v := v) ⟨hZ,hi,hv⟩

/-- ONE actual parent query suffices. Generate the ten actual weak-image
records, both pairs of lifted tables, both actual target bodies, weakened
whole-parent output, native fresh instance, cons table and direct raw-body
query. All twenty construction witnesses are internal; nineteen are
retained and the independent native-instance output is eliminated by the
existing full binder cancellation. -/
theorem produce_quantified {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (universal : Bool)
    (w z a f alpha b A B t R S n x Parent : Fin m)
    (hi : Derives Gamma (quantifiedInput universal w z a f alpha b A B t R S n x Parent)) :
    Derives Gamma (quantifiedProduced universal w z a f alpha b A B t R S n x Parent) := by
  have hw := Derives.conjL hi
  have hB := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  have query := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi)))))))
  have lists := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ w R S a f z b n Parent hw query)
  have he := ForcingWeakenedImages.produce hZ w a f z b B R S (.conjI hw (.conjI hB lists))
  let E := ForcingWeakenedImages.data (old 10 w) (old 10 a) (old 10 f) (old 10 z) (old 10 b) (old 10 B)
    (old 10 R) (old 10 S) (slot 10)
  let Delta := Context.add E (raisedContext 10 Gamma)
  apply HornBinderRules.eliminate_many 10 E _ he
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have h : Inputs Delta
      ⟨universal,old 10 w,old 10 z,old 10 a,old 10 f,old 10 alpha,old 10 b,old 10 A,old 10 B,
        old 10 t,old 10 R,old 10 S,old 10 n,old 10 x,old 10 Parent⟩ (slot 10) :=
    ⟨HornBinderRules.zf_body 10 hZ E,
      of_eq (quantifiedInput_rename universal w z a f alpha b A B t R S n x Parent (old 10)) (HornBinderRules.under_body 10 hi E),hE⟩
  have ho := at_images h
  have result : Derives Delta (quantifiedProduced universal (old 10 w) (old 10 z) (old 10 a) (old 10 f) (old 10 alpha)
      (old 10 b) (old 10 A) (old 10 B) (old 10 t) (old 10 R) (old 10 S) (old 10 n) (old 10 x) (old 10 Parent)) := by
    apply HornBinderRules.intro_many 10 _ (slot 10)
    exact of_eq (by simp only [quantifiedBody, quantifiedAtImages_rename, assign_old, assign_slot]) ho
  exact of_eq (quantifiedProduced_rename universal w z a f alpha b A B t R S n x Parent (old 10)).symm result

def input {m} (w z a f alpha b A B t R S n x Parent : Fin m) : Formula m :=
  quantifiedInput true w z a f alpha b A B t R S n x Parent

theorem input_rename {m l} (w z a f alpha b A B t R S n x Parent : Fin m) (rho : Fin m → Fin l) :
    (input w z a f alpha b A B t R S n x Parent).rename rho =
      input (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) :=
  quantifiedInput_rename true w z a f alpha b A B t R S n x Parent rho

def data {m} (w z a f alpha b A B t R S n x Parent : Fin m) (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Formula m :=
  quantifiedData true w z a f alpha b A B t R S n x Parent v u

theorem data_rename {m l} (w z a f alpha b A B t R S n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (rho : Fin m → Fin l) :
    (data w z a f alpha b A B t R S n x Parent v u).rename rho =
      data (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) (fun i => rho (u i)) :=
  quantifiedData_rename true w z a f alpha b A B t R S n x Parent v u rho

def atImages {m} (w z a f alpha b A B t R S n x Parent : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  quantifiedAtImages true w z a f alpha b A B t R S n x Parent v

theorem atImages_rename {m l} (w z a f alpha b A B t R S n x Parent : Fin m)
    (v : Fin 10 → Fin m) (rho : Fin m → Fin l) :
    (atImages w z a f alpha b A B t R S n x Parent v).rename rho =
      atImages (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) :=
  quantifiedAtImages_rename true w z a f alpha b A B t R S n x Parent v rho

def body {m} (w z a f alpha b A B t R S n x Parent : Fin m) : Formula (m+10) :=
  quantifiedBody true w z a f alpha b A B t R S n x Parent

def produced {m} (w z a f alpha b A B t R S n x Parent : Fin m) : Formula m :=
  quantifiedProduced true w z a f alpha b A B t R S n x Parent

theorem produced_rename {m l} (w z a f alpha b A B t R S n x Parent : Fin m) (rho : Fin m → Fin l) :
    (produced w z a f alpha b A B t R S n x Parent).rename rho =
      produced (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho n) (rho x) (rho Parent) :=
  quantifiedProduced_rename true w z a f alpha b A B t R S n x Parent rho

theorem produce_at_images {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z a f alpha b A B t R S n x Parent : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Gamma (input w z a f alpha b A B t R S n x Parent))
    (hv : Derives Gamma (ForcingWeakenedImages.data w a f z b B R S v)) :
    Derives Gamma (atImages w z a f alpha b A B t R S n x Parent v) :=
  produce_quantified_at_images hZ true w z a f alpha b A B t R S n x Parent v hi hv

theorem produce {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z a f alpha b A B t R S n x Parent : Fin m) (hi : Derives Gamma (input w z a f alpha b A B t R S n x Parent)) :
    Derives Gamma (produced w z a f alpha b A B t R S n x Parent) :=
  produce_quantified hZ true w z a f alpha b A B t R S n x Parent hi

def sentence {m} (w z a f alpha b A B t R S n x Parent : Fin m) : Source.Sentence :=
  ((input w z a f alpha b A B t R S n x Parent).imp
    (produced w z a f alpha b A B t R S n x Parent)).close

theorem kernel_certificate {m} (w z a f alpha b A B t R S n x Parent : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence w z a f alpha b A B t R S n x Parent)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) w z a f alpha b A B t R S n x Parent (.hyp (Or.inl rfl))

/-- Consume the actual opened record together with the original nested
Root record at its SAME raw-query body. Identifying the concrete member,
order and tail outputs with the canonical nested producer is still the
source caller's obligation; no such identification is asserted here. -/
theorem consume_opened {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (test : Formula 1)
    (w z a f alpha b A B t R S n x Parent G W M O Tail I J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (ho : Derives Gamma (data w z a f alpha b A B t R S n x Parent v u))
    (hd : Derives Gamma (ForcingNestedGuardProof.data test w z b A B G W M O Tail I (u 8) J)) :
    Derives Gamma (InternalProofBackground.implication test w z b G Parent) := by
  have tail := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR
      ho)))))))))
  exact ForcingFreshOpeningInverse.consume_nested hZ test w z b A B t (u 4) (u 5) G W M O Tail I (u 8) J Parent
    (.conjL (.conjR tail)) hd (.conjL tail)

def consumeSentence {m} (test : Formula 1)
    (w z a f alpha b A B t R S n x Parent G W M O Tail I J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Source.Sentence :=
  (((data w z a f alpha b A B t R S n x Parent v u).conj
    (ForcingNestedGuardProof.data test w z b A B G W M O Tail I (u 8) J)).imp
      (InternalProofBackground.implication test w z b G Parent)).close

theorem consume_kernel_certificate {m} (test : Formula 1)
    (w z a f alpha b A B t R S n x Parent G W M O Tail I J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (consumeSentence test w z a f alpha b A B t R S n x Parent G W M O Tail I J v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact consume_opened (ZFContext.add (ZFContext.source_ZF m) _) test
    w z a f alpha b A B t R S n x Parent G W M O Tail I J v u (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

/-- Runtime metadata and ONE actual whole-parent query, without a supplied
source body or body constructor. The full fragment compilers below produce
that source body internally from their literal outer ALL. -/
def frame {m} (w z a f alpha b A B t R S n Parent : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor alpha a).conj
    ((successor A z).conj ((successor B b).conj
      ((SyntaxVariableSyntax.code false w z t).conj
        ((SyntaxTermSyntax.term w z B t).conj
          (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z b n Parent)))))))

theorem frame_rename {m l} (w z a f alpha b A B t R S n Parent : Fin m) (rho : Fin m → Fin l) :
    (frame w z a f alpha b A B t R S n Parent).rename rho =
      frame (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho Parent) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxTermSyntax.term_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def compiledOpened {m} (w z a f alpha b A B t R S n Parent : Fin m) : Formula m := .ex
  (produced w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc A.castSucc B.castSucc
    t.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) Parent.castSucc)

theorem compiledOpened_rename {m l} (w z a f alpha b A B t R S n Parent : Fin m) (rho : Fin m → Fin l) :
    (compiledOpened w z a f alpha b A B t R S n Parent).rename rho =
      compiledOpened (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho n) (rho Parent) := by
  simp only [compiledOpened, Formula.rename, produced_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem from_body {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z a f alpha b A B t R S n Parent : Fin m)
    (hf : Derives Gamma (frame w z a f alpha b A B t R S n Parent))
    (hb : Derives Gamma (ForcingNegCode.bodyOutput w alpha f n)) :
    Derives Gamma (compiledOpened w z a f alpha b A B t R S n Parent) := by
  let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) n.castSucc).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) alpha.castSucc f.castSucc)
  let Delta := Context.add E (Context.image Formula.raise Gamma)
  apply Derives.exE (p := E) hb
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have h := of_eq (frame_rename w z a f alpha b A B t R S n Parent Fin.castSucc) (SourceLogic.under hf E)
  have h1 := Derives.conjR h
  have h2 := Derives.conjR h1
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  have h6 := Derives.conjR h5
  have hi : Derives Delta (input w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc
      A.castSucc B.castSucc t.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) Parent.castSucc) :=
    .conjI (.conjL h) (.conjI (.conjL h1) (.conjI (.conjL h2) (.conjI (.conjL h3)
      (.conjI (.conjL h4) (.conjI (.conjL h5) (.conjI (.conjL h6) (.conjI (.conjL hE) (.conjR h6))))))))
  have ho := produce (ZFContext.under hZ E) w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc
    A.castSucc B.castSucc t.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) Parent.castSucc hi
  have result : Derives Delta (compiledOpened w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc
      A.castSucc B.castSucc t.castSucc R.castSucc S.castSucc n.castSucc Parent.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, produced_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho
  exact of_eq (compiledOpened_rename w z a f alpha b A B t R S n Parent Fin.castSucc).symm result

def negativeInput {k m} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n Parent : Fin m) : Formula m :=
  (frame w z a f alpha b A B t R S n Parent).conj (ForcingNegCode.compiled Reln w a alpha f j N n)

theorem negativeInput_rename {k m l} (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S j N n Parent : Fin m) (rho : Fin m → Fin l) :
    (negativeInput Reln w z a f alpha b A B t R S j N n Parent).rename rho =
      negativeInput Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho j) (rho N) (rho n) (rho Parent) := by
  simp only [negativeInput, Formula.rename, frame_rename, ForcingNegCode.compiled_rename]

/-- Complete original negative compiler plus its actual parent query;
the source body and all twenty opening witnesses are internally generated. -/
theorem from_negative {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S j N n Parent : Fin m)
    (hi : Derives Gamma (negativeInput Reln w z a f alpha b A B t R S j N n Parent)) :
    Derives Gamma (compiledOpened w z a f alpha b A B t R S n Parent) :=
  from_body hZ w z a f alpha b A B t R S n Parent (.conjL hi)
    (ForcingNegCode.body_output Reln w a alpha f j N n (.conjR hi))

def negativeSentence {k m} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n Parent : Fin m) : Source.Sentence :=
  ((negativeInput Reln w z a f alpha b A B t R S j N n Parent).imp
    (compiledOpened w z a f alpha b A B t R S n Parent)).close

theorem negative_kernel_certificate {k m} (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S j N n Parent : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (negativeSentence Reln w z a f alpha b A B t R S j N n Parent)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_negative (ZFContext.add (ZFContext.source_ZF m) _) Reln w z a f alpha b A B t R S j N n Parent (.hyp (Or.inl rfl))

private theorem exist_body {k m} {Gamma : Context m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w a alpha beta gamma f j N n : Fin m)
    (hc : Derives Gamma (ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n)) :
    Derives Gamma (ForcingNegCode.bodyOutput w alpha f n) := by
  let E := ForcingExistCode.body Reln Dom w a alpha beta gamma f j N n
  let Delta := Context.add E (raisedContext 8 Gamma)
  apply HornBinderRules.eliminate_many 8 E _ (.conjR hc)
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  let F := ForcingExistCode.shellBody (old 8 w) (old 8 a) (old 8 alpha) (old 8 beta) (old 8 gamma)
    (old 8 f) (slot 8 2) (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 n)
  let Xi := Context.add F (raisedContext 7 Delta)
  have shell := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hE))))))
  have result : Derives Delta (ForcingNegCode.bodyOutput (old 8 w) (old 8 alpha) (old 8 f) (old 8 n)) := by
    apply HornBinderRules.eliminate_many 7 F _ shell
    have hF : Derives Xi F := .hyp (Or.inl rfl)
    have node6 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hF))))))
    have allNode := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hF))))))
    have out : Derives Xi (ForcingNegCode.bodyOutput (old 7 (old 8 w)) (old 7 (old 8 alpha))
        (old 7 (old 8 f)) (old 7 (old 8 n))) := by
      apply Derives.exI (slot 7 6)
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
        FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
        (.conjI (.conjL allNode) (.conjR node6))
    exact of_eq (ForcingNegCode.bodyOutput_rename (old 8 w) (old 8 alpha) (old 8 f) (old 8 n) (old 7)).symm out
  exact of_eq (ForcingNegCode.bodyOutput_rename w alpha f n (old 8)).symm result

def existentialInput {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n Parent : Fin m) : Formula m :=
  (frame w z a f alpha b A B t R S n Parent).conj (ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n)

theorem existentialInput_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n Parent : Fin m) (rho : Fin m → Fin l) :
    (existentialInput Reln Dom w z a f alpha beta gamma b A B t R S j N n Parent).rename rho =
      existentialInput Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A) (rho B)
        (rho t) (rho R) (rho S) (rho j) (rho N) (rho n) (rho Parent) := by
  simp only [existentialInput, Formula.rename, frame_rename, ForcingExistCode.compiled_rename]

/-- Complete original existential compiler plus its actual parent query;
all original eight compiler and seven shell witnesses are consumed. -/
theorem from_existential {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n Parent : Fin m)
    (hi : Derives Gamma (existentialInput Reln Dom w z a f alpha beta gamma b A B t R S j N n Parent)) :
    Derives Gamma (compiledOpened w z a f alpha b A B t R S n Parent) :=
  from_body hZ w z a f alpha b A B t R S n Parent (.conjL hi)
    (exist_body Reln Dom w a alpha beta gamma f j N n (.conjR hi))

def existentialSentence {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n Parent : Fin m) : Source.Sentence :=
  ((existentialInput Reln Dom w z a f alpha beta gamma b A B t R S j N n Parent).imp
    (compiledOpened w z a f alpha b A B t R S n Parent)).close

theorem existential_kernel_certificate {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n Parent : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (existentialSentence Reln Dom w z a f alpha beta gamma b A B t R S j N n Parent)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_existential (ZFContext.add (ZFContext.source_ZF m) _) Reln Dom
    w z a f alpha beta gamma b A B t R S j N n Parent (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingFreshParentOpening
