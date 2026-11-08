/- Type preservation of the ORIGINAL tag-9 closure at EVERY internal count.
Consume the existing recursion, equations, omega induction and addition; no new
recursor or standard-code restriction. The finite schema-shell typing remains
an explicit separate consumer, not an assumed final axiom-test result. -/
import PPAC.Migration.SchemaAxiomCompilation
import PPAC.Migration.Internal.FormulaCodeKnownLogical
import PPAC.Migration.Internal.FormulaCodeTransport
import PPAC.Migration.Internal.OriginalUniversalBlock
import PPAC.Migration.Internal.NaturalAdditionShift

namespace PPAC.Migration.SchemaClosureTyping
open Source SourceAlgebra SourceLogic OmegaSyntax
open PPAC.Migration.Internal
open PPAC.Migration.Internal.HornBinderSyntax
open PPAC.Migration.Internal.SyntaxRenameQuerySyntax (of_eq)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Remaining bound context b plus closure count n is the original context d. -/
def point {m} (w n a d b f out : Fin m) : Source.Formula m :=
  (Source.Formula.mem b w).imp ((NaturalAdditionSyntax.sum w b n d).imp
    ((FormulaCodeSyntax.formulaCode w a d f).imp
      ((SyntaxUnaryIterationSyntax.forallClosure w a n out).imp (FormulaCodeSyntax.formulaCode w out b f))))

def property {m} (w n : Fin m) : Source.Formula m := OriginalUniversalBlock.allMany 5
  (point (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4))

theorem point_rename {m l} (w n a d b f out : Fin m) (r : Fin m → Fin l) :
    (point w n a d b f out).rename r = point (r w) (r n) (r a) (r d) (r b) (r f) (r out) := by
  simp only [point,Formula.rename,NaturalAdditionSyntax.sum_rename,
    FormulaCodeSyntax.formulaCode_rename,SyntaxUnaryIterationSyntax.forallClosure_rename]

theorem property_rename {m l} (w n : Fin m) (r : Fin m → Fin l) :
    (property w n).rename r = property (r w) (r n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,point_rename,lift_old,lift_slot]

def matrix : Source.Formula 2 := property 0 1

theorem matrix_pred {m} (r : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred matrix r x = property (r 0) x := by
  have h0 : Fin.lastCases x r (0 : Fin 2) = r 0 := by
    change Fin.lastCases x r (0 : Fin 1).castSucc = r 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x r (1 : Fin 2) = x := by
    change Fin.lastCases x r (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,property_rename,h0,h1]

theorem property_at {m} {Γ : Context m} (w n a d b f out : Fin m)
    (h : Derives Γ (property w n)) (hb : Derives Γ (Source.Formula.mem b w))
    (hd : Derives Γ (NaturalAdditionSyntax.sum w b n d)) (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a d f))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out b f) := by
  let env : Fin 5 → Fin m := Fin.cases a (Fin.cases d (Fin.cases b (Fin.cases f (fun _ => out))))
  have hh := OriginalUniversalBlock.at_many 5 _ env h
  have hp : Derives Γ (point w n a d b f out) := of_eq (by
    simp only [point_rename,assign_old,assign_slot]; rfl) hh
  exact .impE (.impE (.impE (.impE hp hb) hd) ha) ho

private theorem zero_point {m} {Γ : Context m} (w n a d b f out : Fin m)
    (hz : Derives Γ (empty n)) (hd : Derives Γ (NaturalAdditionSyntax.sum w b n d))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a d f))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out b f) := by
  have hdEq := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w) w b n d hz hd
  have hoEq := NaturalRecursionLaws.evaluation_zero (SyntaxUnaryIterationStep.matrix 9) (SyntaxUnaryIterationSyntax.params w) w a n out hz ho
  exact FormulaCodeTransport.code_root w a b f out (eq_symm hoEq) (FormulaCodeTransport.code_bound w a d f b hdEq ha)

private theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n s a d b f out bp t v : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w))
    (hs : Derives Γ (successor s n)) (hi : Derives Γ (property w n)) (hb : Derives Γ (Source.Formula.mem b w))
    (hd : Derives Γ (NaturalAdditionSyntax.sum w b s d)) (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a d f))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a s out)) (hbp : Derives Γ (successor bp b))
    (ht : Derives Γ (NaturalAdditionSyntax.sum w b n t)) (hv : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n v)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out b f) := by
  have hdStep := ZFArithmetic.add_succ_forward hZ w b n s t d hw hb hn hs ht hd
  have hsum := NaturalAdditionShift.shift_at (ZFContext.arithmetic hZ) w b bp n t d
    (ZFContext.recAdd hZ) (ZFContext.separation hZ NaturalAdditionShift.matrix) hw hb hbp hn ht hdStep
  have hbpW := OmegaStructureAlgebra.successor_member w bp b (ZFContext.arithmetic hZ).base.extensionality hw hb hbp
  have htyped := property_at w n a d bp f v hi hbpW hsum ha hv
  have hguards := FormulaCodeProperties.guards w a d f ha
  have hnode := SyntaxUnaryIterationLaws.successor_forward hZ 9 w a n s v out hw (.conjL hguards) hn hs hv ho
  exact .impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ true w b f v out bp hw hnode hbp))
    (.conjI (.conjI hb (.conjR (.conjR hguards))) htyped)

private theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n s a d b f out : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w))
    (hs : Derives Γ (successor s n)) (hi : Derives Γ (property w n)) (hb : Derives Γ (Source.Formula.mem b w))
    (hd : Derives Γ (NaturalAdditionSyntax.sum w b s d)) (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a d f))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a s out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out b f) := by
  let B := (Source.Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.impE (OmegaSyntax.step_at w b (.conjL hw)) hb)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  let T := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) (ZFArithmetic.add_exists hZ1 w.castSucc b.castSucc n.castSucc hw1 (under hb B) (under hn B))
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 T
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
  have ha2 : Derives Ξ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,FormulaCodeSyntax.formulaCode_rename]) (under (under ha B) T)
  let V := (Source.Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Ω := Context.add V (Context.image Formula.raise Ξ)
  apply Derives.exE (p := V) (SyntaxUnaryIterationCore.exists_iteration hZ2 9 w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc
    hw2 (.conjL (FormulaCodeProperties.guards _ _ _ _ ha2)) (under (under hn B) T))
  have hV : Derives Ω V := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 V)
  have hn3 := under (under (under hn B) T) V
  have hb3 := under (under (under hb B) T) V
  have hs3 : Derives Ω (successor s.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise,successor_rename]) (under (under (under hs B) T) V)
  have hi3 : Derives Ω (property w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise,property_rename]) (under (under (under hi B) T) V)
  have hd3 : Derives Ω (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise,NaturalAdditionSyntax.sum_rename]) (under (under (under hd B) T) V)
  have ha3 := of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ Fin.castSucc) (under ha2 V)
  have ho3 : Derives Ω (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc out.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise,SyntaxUnaryIterationSyntax.forallClosure_rename]) (under (under (under ho B) T) V)
  have hbp3 : Derives Ω (successor (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,successor_rename]) (under (under (.conjR hB) T) V)
  have ht3 : Derives Ω ((Source.Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj
      (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc)) := of_eq (by simp only [T,Formula.raise,Formula.rename,NaturalAdditionSyntax.sum_rename]) (under hT V)
  have hout := advance (ZFContext.under hZ2 V) w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
    a.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc out.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hn3 hs3 hi3 hb3 hd3 ha3 ho3 hbp3 (.conjR ht3) (.conjR hV)
  exact of_eq (by simp only [Formula.raise,FormulaCodeSyntax.formulaCode_rename]) hout

private theorem zero_property {m} {Γ : Context m} (w n : Fin m) (hz : Derives Γ (empty n)) : Derives Γ (property w n) := by
  apply OriginalUniversalBlock.intro_many 5
  have hz5 := of_eq (empty_rename n (old 5)) (HornBinderRules.under_many 5 hz)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact zero_point (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
    (add (add (add (add hz5 _) _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hi : Derives Γ (property w n))
    (hs : Derives Γ (successor s n)) : Derives Γ (property w s) := by
  apply OriginalUniversalBlock.intro_many 5
  have hZ5 := HornBinderRules.zf_many 5 hZ
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_many 5 hw)
  have hn5 := HornBinderRules.under_many 5 hn
  have hi5 := of_eq (property_rename w n (old 5)) (HornBinderRules.under_many 5 hi)
  have hs5 := of_eq (successor_rename s n (old 5)) (HornBinderRules.under_many 5 hs)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_point (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ5 _) _) _) _)
    (old 5 w) (old 5 n) (old 5 s) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
    (add (add (add (add hw5 _) _) _) _) (add (add (add (add hn5 _) _) _) _)
    (add (add (add (add hs5 _) _) _) _) (add (add (add (add hi5 _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem base {m} {Γ : Context m} (w : Fin m) : Derives Γ (OmegaInductionSyntax.base matrix (fun _ : Fin 1 => w)) := by
  simp only [OmegaInductionSyntax.base,matrix_pred,ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.impI
  exact zero_property w.castSucc (Fin.last m) (.hyp (Or.inl rfl))

private theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.step matrix (fun _ : Fin 1 => w) w) := by
  simp only [OmegaInductionSyntax.step,matrix_pred,ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.allI
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (omega w.castSucc.castSucc) :=
    of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add hZ2 _) _) _) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add (add hw2 _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

/-- Genuine object omega induction; includes all internal nonstandard counts. -/
theorem all_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Source.Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hi := ZFArithmetic.induction hZ matrix (fun _ : Fin 1 => w) w hw (base w) (step hZ w hw)
  exact of_eq (by simp only [OmegaInductionSyntax.holds,matrix_pred,ReplacementPredicates.paramsUp]) hi

theorem typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a d b f out : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hb : Derives Γ (Source.Formula.mem b w))
    (hd : Derives Γ (NaturalAdditionSyntax.sum w b n d)) (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a d f))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n out)) : Derives Γ (FormulaCodeSyntax.formulaCode w out b f) := by
  have hi := Derives.allE n (all_typed hZ w hw)
  have hp : Derives Γ ((Source.Formula.mem n w).imp (property w n)) := of_eq (by
    simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hi
  exact property_at w n a d b f out (.impE hp hn) hb hd ha ho

/-- Exact full closure: context n becomes empty after n ORIGINAL forall steps. -/
theorem closed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a z out : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a n z))
    (ho : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n out)) : Derives Γ (FormulaCodeSyntax.formulaCode w out z z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hsum := ZFArithmetic.add_commute hZ w n z n hw hn hzW (ZFArithmetic.add_zero hZ w n z hw hn hz)
  exact typed hZ w n a n z z out hw hn hzW hsum ha ho

def sentence {m} (w n a z out : Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem n w).imp ((empty z).imp ((FormulaCodeSyntax.formulaCode w a n z).imp
    ((SyntaxUnaryIterationSyntax.forallClosure w a n out).imp (FormulaCodeSyntax.formulaCode w out z z)))))).close

theorem source_certificate {m} (w n a z out : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sentence w n a z out) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (SyntaxUnaryIterationSyntax.forallClosure w a n out)
    (Context.add (FormulaCodeSyntax.formulaCode w a n z) (Context.add (empty z)
      (Context.add (Source.Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _
  exact closed hZ w n a z out (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} (w n a z out : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w n a z out)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate w n a z out))


/-- Actual whole closure, closed-formula type and uniqueness on ALL candidates. -/
def closedFiber {m} (w n a z : Fin m) : Source.Formula m := .ex
  (((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxUnaryIterationSyntax.forallClosure w.castSucc a.castSucc n.castSucc (Fin.last m))).conj
      ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) z.castSucc z.castSucc).conj
        (.all ((SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
          (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))))

theorem closedFiber_rename {m l} (w n a z : Fin m) (r : Fin m → Fin l) :
    (closedFiber w n a z).rename r = closedFiber (r w) (r n) (r a) (r z) := by
  simp only [closedFiber,Formula.rename,SyntaxUnaryIterationSyntax.forallClosure_rename,
    FormulaCodeSyntax.formulaCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Consumes the existing original recursor's actual unique output; no given
output, trace, typed-output oracle or external standard count. -/
theorem closed_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a n z)) : Derives Γ (closedFiber w n a z) := by
  let B := ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxUnaryIterationSyntax.forallClosure w.castSucc a.castSucc n.castSucc (Fin.last m))).conj
      (.all ((SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxUnaryIterationCore.exists_unique hZ 9 w a n hw
    (.conjL (FormulaCodeProperties.guards _ _ _ _ ha)) hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := closed (ZFContext.under hZ B) w.castSucc n.castSucc a.castSucc z.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (under hn B)
    (of_eq (empty_rename z Fin.castSucc) (under hz B))
    (of_eq (FormulaCodeSyntax.formulaCode_rename w a n z Fin.castSucc) (under ha B)) (.conjR (.conjL hB))
  have hout : Derives Δ (closedFiber w.castSucc n.castSucc a.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxUnaryIterationSyntax.forallClosure_rename,
      FormulaCodeSyntax.formulaCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (.conjI (.conjL hB) (.conjI ht (.conjR hB)))
  exact of_eq (closedFiber_rename w n a z Fin.castSucc).symm hout

def fiber_sentence {m} (w n a z : Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem n w).imp ((empty z).imp
    ((FormulaCodeSyntax.formulaCode w a n z).imp (closedFiber w n a z))))).close

theorem fiber_source_certificate {m} (w n a z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiber_sentence w n a z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (FormulaCodeSyntax.formulaCode w a n z) (Context.add (empty z)
    (Context.add (Source.Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _
  exact closed_fiber hZ w n a z (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate {m} (w n a z : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (fiber_sentence w n a z)) :=
  ZFReplay.replay (TheoryTransport.sentence (fiber_source_certificate w n a z))

end PPAC.Migration.SchemaClosureTyping
