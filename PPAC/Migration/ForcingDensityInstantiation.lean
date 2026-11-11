import PPAC.Migration.ForcingDensityCode
import PPAC.Migration.ForcingExistTailOpening
import PPAC.Migration.Internal.ProjectCompilerUniqueTransport
import PPAC.Migration.ForcingRawModalBody
import PPAC.Migration.NativeProofQuotation

/-! The outer ALL of the original force_of_dense premise is instantiated in
the actual target scope, at the selected condition term. The two guards and
existential tail are read from the same lifted query. -/
namespace PPAC.Migration.ForcingDensityInstantiation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
open NativeProofQuotation (eliminate_objects)

set_option maxRecDepth 16384

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false


/-- Native instantiation and the two actual implication constructors in its
result, with all three subqueries made under the very same native table. -/
def pointData {m} (w z b U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (successor (v 0) z).conj
    ((SyntaxTopFormulaSyntax.instantiateState w z b (v 0) p U (v 1) (v 2) (v 3)).conj
      ((ForcingRawModalBody.outputs w (v 2) (v 3) (v 0) b z b M O Tail I (v 1)).conj
        (implication test w z b G (v 1))))

theorem pointData_rename {m l} (w z b U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (pointData w z b U p G M O Tail I v).rename ρ =
      pointData (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) (fun i => ρ (v i)) := by
  simp only [pointData, Formula.rename, successor_rename, SyntaxTopFormulaSyntax.instantiateState_rename,
    ForcingRawModalBody.outputs_rename, implication_rename]

def point {m} (w z b U p G M O Tail I : Fin m) : Formula m :=
  existsMany 4 (pointData (old 4 w) (old 4 z) (old 4 b) (old 4 U) (old 4 p) (old 4 G)
    (old 4 M) (old 4 O) (old 4 Tail) (old 4 I) (slot 4))

theorem point_rename {m l} (w z b U p G M O Tail I : Fin m) (ρ : Fin m → Fin l) :
    (point w z b U p G M O Tail I).rename ρ =
      point (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) := by
  simp only [point, existsMany_rename, pointData_rename, lift_old, lift_slot]

private theorem at_instance_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U p G M O Tail I C N : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I U)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hC : Derives Γ (successor C z))
    (hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b C p U N))
    (hp : Derives Γ (implication test w z b G N)) :
    Derives Γ (point w z b U p G M O Tail I) := by
  let out := point w z b U p G M O Tail I
  refine eliminate_objects hZ 2 (fun ρ v =>
    SyntaxTopFormulaSyntax.instantiateState (ρ w) (ρ z) (ρ b) (ρ C) (ρ p) (ρ U) (ρ N) (v 0) (v 1))
    ?_ out ?_
  · exact hInst
  intro l Δ ρ v hZ1 lift hSubst
  have hGuards := ForcingRawModalBody.from_query hZ1 (ρ w) (v 0) (v 1) (ρ C) (ρ b) (ρ z) (ρ b)
    (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ U) (ρ N)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho)) (.conjR hSubst)
  apply of_eq (point_rename w z b U p G M O Tail I ρ).symm
  let fields : Fin 4 → Fin l := Fin.cases (ρ C) (Fin.cases (ρ N) v)
  apply HornBinderRules.intro_many 4 _ fields
  have hd : Derives Δ (pointData (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G)
      (ρ M) (ρ O) (ρ Tail) (ρ I) fields) :=
    .conjI (of_eq (successor_rename _ _ _) (lift hC))
      (.conjI hSubst (.conjI hGuards (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))))
  exact of_eq (by simp only [pointData_rename, assign_old, assign_slot]) hd

private theorem point_from_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U p G M O Tail I : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I U)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G)) :
    Derives Γ (point w z b U p G M O Tail I) := by
  let out := point w z b U p G M O Tail I
  refine eliminate_objects hZ 3 (fun ρ v =>
    (successor (v 0) (ρ z)).conj ((SyntaxTopFormulaSyntax.instantiated (ρ w) (ρ z) (ρ b)
      (v 0) (ρ p) (ρ U) (v 1)).conj ((SyntaxNodeSyntax.constructor 2 7 (ρ w)
        (SyntaxAtomSyntax.two (ρ G) (v 1)) (v 2)).conj (proved test (ρ w) (ρ z) (ρ b) (v 2)))))
    hInst out ?_
  intro l Δ ρ v hZ1 lift hv
  have hp : Derives Δ (implication test (ρ w) (ρ z) (ρ b) (ρ G) (v 1)) := by
    apply Derives.exI (v 2)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjR (.conjR hv))
  exact of_eq (point_rename w z b U p G M O Tail I ρ).symm
    (at_instance_tables hZ1 (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) (v 0) (v 1)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho)) (.conjL hv) (.conjL (.conjR hv)) hp)

def pointGuardsData {m} (w z A f C b K H U p G M O Tail I : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingRawModalBody.data w K H A f C b M O Tail I U v).conj
    (point w z b U p G (v 1) (v 2) (v 3) (v 0))

theorem pointGuardsData_rename {m l} (w z A f C b K H U p G M O Tail I : Fin m) (v : Fin 4 → Fin m)
    (ρ : Fin m → Fin l) :
    (pointGuardsData w z A f C b K H U p G M O Tail I v).rename ρ =
      pointGuardsData (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (fun i => ρ (v i)) := by
  simp only [pointGuardsData, Formula.rename, ForcingRawModalBody.data_rename, point_rename]

def pointGuards {m} (w z A f C b K H U p G M O Tail I : Fin m) : Formula m :=
  existsMany 4 (pointGuardsData (old 4 w) (old 4 z) (old 4 A) (old 4 f) (old 4 C) (old 4 b)
    (old 4 K) (old 4 H) (old 4 U) (old 4 p) (old 4 G) (old 4 M) (old 4 O) (old 4 Tail) (old 4 I) (slot 4))

theorem pointGuards_rename {m l} (w z A f C b K H U p G M O Tail I : Fin m) (ρ : Fin m → Fin l) :
    (pointGuards w z A f C b K H U p G M O Tail I).rename ρ =
      pointGuards (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) := by
  simp only [pointGuards, existsMany_rename, pointGuardsData_rename, lift_old, lift_slot]

private theorem point_guards {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A f C b K H U p G M O Tail I : Fin m) (hw : Derives Γ (omega w))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G))
    (hRaw : Derives Γ (ForcingRawModalBody.outputs w K H A f C b M O Tail I U)) :
    Derives Γ (pointGuards w z A f C b K H U p G M O Tail I) := by
  let out := pointGuards w z A f C b K H U p G M O Tail I
  refine eliminate_objects hZ 4 (fun ρ v => ForcingRawModalBody.data (ρ w) (ρ K) (ρ H) (ρ A)
    (ρ f) (ρ C) (ρ b) (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ U) v) hRaw out ?_
  intro l Δ ρ v hZ1 lift hv
  have hAt := point_from_proof hZ1 (ρ w) (ρ z) (ρ b) (ρ U) (ρ p) (ρ G) (v 1) (v 2) (v 3) (v 0)
    (of_eq (omega_rename _ _) (lift hw)) (.conjL (.conjL hv)) (.conjL (.conjR hv))
    (of_eq (InternalProofQuantifier.guardedInstance_rename _ _ _ _ _ _ _ _) (lift hInst))
  apply of_eq (pointGuards_rename w z A f C b K H U p G M O Tail I ρ).symm
  apply HornBinderRules.intro_many 4 _ v
  have hd : Derives Δ (pointGuardsData (ρ w) (ρ z) (ρ A) (ρ f) (ρ C) (ρ b) (ρ K) (ρ H) (ρ U)
      (ρ p) (ρ G) (ρ M) (ρ O) (ρ Tail) (ρ I) v) := .conjI hv hAt
  exact of_eq (by simp only [pointGuardsData_rename, assign_old, assign_slot]) hd

/-- Actual target body, its two implications in the lifted environment, and
an instance proof under the very same background. -/
def openedData {m} (w z a f b L S E p G M O Tail I X : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (singleCode 9 w (v 0) E).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w L S a f z b (v 1) (v 2) (v 3) (v 4)).conj
      ((substituted w (v 3) (v 4) (v 1) f (v 2) b X (v 0)).conj
        (pointGuards w z (v 1) f (v 2) b (v 3) (v 4) (v 0) p G M O Tail I)))

theorem openedData_rename {m l} (w z a f b L S E p G M O Tail I X : Fin m) (v : Fin 5 → Fin m)
    (ρ : Fin m → Fin l) :
    (openedData w z a f b L S E p G M O Tail I X v).rename ρ =
      openedData (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ E) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ X) (fun i => ρ (v i)) := by
  simp only [openedData, Formula.rename, singleCode_rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    substituted_rename, pointGuards_rename]

def opened {m} (w z a f b L S E p G M O Tail I X : Fin m) : Formula m :=
  existsMany 5 (openedData (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 b) (old 5 L) (old 5 S)
    (old 5 E) (old 5 p) (old 5 G) (old 5 M) (old 5 O) (old 5 Tail) (old 5 I) (old 5 X) (slot 5))

theorem opened_rename {m l} (w z a f b L S E p G M O Tail I X : Fin m) (ρ : Fin m → Fin l) :
    (opened w z a f b L S E p G M O Tail I X).rename ρ =
      opened (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ E) (ρ p) (ρ G)
        (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ X) := by
  simp only [opened, existsMany_rename, openedData_rename, lift_old, lift_slot]

private theorem guarded_at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b U E p G : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hE : Derives Γ (formulaCode w E z b)) (hU : Derives Γ (singleCode 9 w U E))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E)) :
    Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G) := by
  let B := (SyntaxNodeSyntax.constructor 2 7 w.castSucc
    (SyntaxAtomSyntax.two G.castSucc E.castSucc) (Fin.last m)).conj
      (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  apply Derives.exE (p := B) hp
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (InternalProofQuantifier.guardedInstance_rename test w z b U p G Fin.castSucc).symm
    (InternalProofQuantifier.guarded_instantiate (ZFContext.under hZ B) test w.castSucc z.castSucc b.castSucc
      U.castSucc p.castSucc E.castSucc G.castSucc (Fin.last m)
      (of_eq (omega_rename _ _) (under hw B)) (of_eq (empty_rename _ _) (under hz B))
      (of_eq (formulaCode_rename _ _ _ _ _) (under hE B))
      (of_eq (singleCode_rename _ _ _ _ _) (under hU B))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (under ht B))
      (of_eq (formulaCode_rename _ _ _ _ _) (under hG B)) (.conjL hB) (.conjR hB))

private theorem at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S E p G M O Tail I X U : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (binaryCode 2 w M I X)) (ho : Derives Γ (binaryCode 2 w O Tail I))
    (hs : Derives Γ (singleCode 9 w U E))
    (hBody : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check true w X L S a f z b U))
    (hInst : Derives Γ (InternalProofQuantifier.guardedInstance test w z b U p G)) :
    Derives Γ (opened w z a f b L S E p G M O Tail I X) := by
  let out := opened w z a f b L S E p G M O Tail I X
  refine eliminate_objects hZ 4 (fun r v =>
    (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b) (v 0) (v 1) (v 2) (v 3)).conj
      (substituted (r w) (v 2) (v 3) (v 0) (r f) (v 1) (r b) (r X) (r U))) ?_ out ?_
  · exact hBody
  intro l Δ r v hZ1 lift hLift
  have ho2 := ForcingRawModalBody.from_query hZ1 (r w) (v 2) (v 3) (v 0) (r f) (v 1) (r b)
    (r M) (r O) (r Tail) (r I) (r X) (r U) (of_eq (omega_rename _ _) (lift hw))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hm)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift ho))
    (.conjR hLift)
  have hPoint := point_guards hZ1 (r w) (r z) (v 0) (r f) (v 1) (r b) (v 2) (v 3) (r U)
    (r p) (r G) (r M) (r O) (r Tail) (r I) (of_eq (omega_rename _ _) (lift hw))
    (of_eq (InternalProofQuantifier.guardedInstance_rename _ _ _ _ _ _ _ _) (lift hInst)) ho2
  apply of_eq (opened_rename w z a f b L S E p G M O Tail I X r).symm
  let fields : Fin 5 → Fin l := Fin.cases (r U) v
  apply HornBinderRules.intro_many 5 _ fields
  have hd : Derives Δ (openedData (r w) (r z) (r a) (r f) (r b) (r L) (r S) (r E) (r p) (r G)
      (r M) (r O) (r Tail) (r I) (r X) fields) :=
    .conjI (of_eq (singleCode_rename _ _ _ _ _) (lift hs))
      (.conjI (.conjL hLift) (.conjI (.conjR hLift) hPoint))
  exact of_eq (by simp only [openedData_rename, assign_old, assign_slot]) hd

private theorem from_outer {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S D E p G M O Tail I X : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hOuter : Derives Γ (ForcingRawModalBody.shell w D M O Tail I X))
    (hQ : Derives Γ (substituted w L S a f z b D E)) :
    Derives Γ (opened w z a f b L S E p G M O Tail I X) := by
  let P := (singleCode 9 w.castSucc (Fin.last m) E.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc X.castSucc L.castSucc S.castSucc
      a.castSucc f.castSucc z.castSucc b.castSucc (Fin.last m))
  apply Derives.exE (p := P) (ForcingMixedUnary.single_output hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩))
    w L S a f z b D X E hw (.conjL hOuter) hQ)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename _ _) (under hw P)
  have hZ1 := ZFContext.under hZ P
  have hType := SyntaxMixedFormulaJudgment.target_type w L S a f z b D E hQ
  have hI := guarded_at_body hZ1 w.castSucc z.castSucc b.castSucc (Fin.last m) E.castSucc p.castSucc G.castSucc
    hw1 (of_eq (empty_rename _ _) (under hz P)) (of_eq (formulaCode_rename _ _ _ _ _) (under hType P))
    (.conjL hP) (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (under ht P))
    (of_eq (formulaCode_rename _ _ _ _ _) (under hG P)) (of_eq (implication_rename _ _ _ _ _ _ _) (under hp P))
  exact of_eq (opened_rename w z a f b L S E p G M O Tail I X Fin.castSucc).symm
    (at_body hZ1 w.castSucc z.castSucc a.castSucc f.castSucc b.castSucc L.castSucc S.castSucc
      E.castSucc p.castSucc G.castSucc M.castSucc O.castSucc Tail.castSucc I.castSucc X.castSucc
      (Fin.last m) hw1
      (of_eq (binaryCode_rename _ _ _ _ _ _) (under (.conjL (.conjR hOuter)) P))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (under (.conjR (.conjR hOuter)) P))
      (.conjL hP) (.conjR hP) hI)


/-- The outer opened query tied to its actual five shell constructors. -/
def shellInstanceData {m} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (u : Fin 5 → Fin m) : Formula m :=
  (ForcingDensityCode.shellData w a A B f M O rM rO N D u).conj
    (opened w z a f b L S E p G M O (u 2) (u 3) (u 4))

theorem shellInstanceData_rename {m l} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (u : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (shellInstanceData w z a A B f b L S D E p G M O rM rO N u).rename ρ =
      shellInstanceData (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E)
        (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) (fun i => ρ (u i)) := by
  simp only [shellInstanceData, Formula.rename, ForcingDensityCode.shellData_rename, opened_rename]

def shellInstance {m} (w z a A B f b L S D E p G M O rM rO N : Fin m) : Formula m :=
  existsMany 5 (shellInstanceData (old 5 w) (old 5 z) (old 5 a) (old 5 A) (old 5 B)
    (old 5 f) (old 5 b) (old 5 L) (old 5 S) (old 5 D) (old 5 E) (old 5 p) (old 5 G)
    (old 5 M) (old 5 O) (old 5 rM) (old 5 rO) (old 5 N) (slot 5))

theorem shellInstance_rename {m l} (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (ρ : Fin m → Fin l) :
    (shellInstance w z a A B f b L S D E p G M O rM rO N).rename ρ =
      shellInstance (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E)
        (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) := by
  simp only [shellInstance, existsMany_rename, shellInstanceData_rename, lift_old, lift_slot]

private theorem from_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B f b L S D E p G M O rM rO N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hc : Derives Γ (ForcingDensityCode.shell w a A B f M O rM rO N D))
    (hq : Derives Γ (substituted w L S a f z b D E)) :
    Derives Γ (shellInstance w z a A B f b L S D E p G M O rM rO N) := by
  let out := shellInstance w z a A B f b L S D E p G M O rM rO N
  refine eliminate_objects hZ 5 (fun ρ u =>
    ForcingDensityCode.shellData (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) (ρ D) u)
    hc out ?_
  intro l Δ ρ u hZ1 lift hs
  have h4 := Derives.conjR (.conjR (.conjR hs))
  have h5 := Derives.conjR h4
  have hOuter : Derives Δ (ForcingRawModalBody.shell (ρ w) (ρ D) (ρ M) (ρ O) (u 2) (u 3) (u 4)) :=
    .conjI (.conjL (.conjR h5)) (.conjI (.conjL (.conjL h5)) (.conjL (.conjL h4)))
  have hOpen := from_outer hZ1 (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G)
    (ρ M) (ρ O) (u 2) (u 3) (u 4)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))
    hOuter (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hq))
  apply of_eq (shellInstance_rename w z a A B f b L S D E p G M O rM rO N ρ).symm
  apply HornBinderRules.intro_many 5 _ u
  have ho : Derives Δ (shellInstanceData (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S)
    (ρ D) (ρ E) (ρ p) (ρ G) (ρ M) (ρ O) (ρ rM) (ρ rO) (ρ N) u) := .conjI hs hOpen
  exact of_eq (by simp only [shellInstanceData_rename, assign_old, assign_slot]) ho

def instanceData {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (v : Fin 7 → Fin m) : Formula m :=
  (ForcingDensityCode.data Reln w a A B f j N D v).conj
    (shellInstance w z a A B f b L S D E p G (v 2) (v 3) (v 4) (v 5) (v 6))

theorem instanceData_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (v : Fin 7 → Fin m) (ρ : Fin m → Fin l) :
    (instanceData Reln w z a A B f j N b L S D E p G v).rename ρ =
      instanceData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N)
        (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G) (fun i => ρ (v i)) := by
  simp only [instanceData, Formula.rename, ForcingDensityCode.data_rename, shellInstance_rename]

def instanceAt {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m) : Formula m :=
  existsMany 7 (instanceData Reln (old 7 w) (old 7 z) (old 7 a) (old 7 A) (old 7 B) (old 7 f)
    (old 7 j) (old 7 N) (old 7 b) (old 7 L) (old 7 S) (old 7 D) (old 7 E) (old 7 p) (old 7 G) (slot 7))

theorem instanceAt_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E p G : Fin m)
    (ρ : Fin m → Fin l) :
    (instanceAt Reln w z a A B f j N b L S D E p G).rename ρ =
      instanceAt Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L) (ρ S) (ρ D)
        (ρ E) (ρ p) (ρ G) := by
  simp only [instanceAt, existsMany_rename, instanceData_rename, lift_old, lift_slot]

/-- Open the actual density query and instantiate its proof under G. The
compiler, guard outputs and instance all refer to the same original query. -/
theorem from_query {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (n+2))
    (w z a A B f j N b L S D E p G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hq : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)) :
    Derives Γ (instanceAt Reln w z a A B f j N b L S D E p G) := by
  let out := instanceAt Reln w z a A B f j N b L S D E p G
  refine eliminate_objects hZ 7 (fun ρ v => ForcingDensityCode.data Reln (ρ w) (ρ a) (ρ A) (ρ B)
    (ρ f) (ρ j) (ρ N) (ρ D) v) (.conjL hq) out ?_
  intro l Δ ρ v hZ1 lift hc
  have hShell := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hc)))))
  have hOpen := from_shell hZ1 (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ b) (ρ L) (ρ S)
    (ρ D) (ρ E) (ρ p) (ρ G) (v 2) (v 3) (v 4) (v 5) (v 6)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))
    hShell (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift (.conjR hq)))
  apply of_eq (instanceAt_rename Reln w z a A B f j N b L S D E p G ρ).symm
  apply HornBinderRules.intro_many 7 _ v
  have ho : Derives Δ (instanceData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N)
    (ρ b) (ρ L) (ρ S) (ρ D) (ρ E) (ρ p) (ρ G) v) := .conjI hc hOpen
  exact of_eq (by simp only [instanceData_rename, assign_old, assign_slot]) ho


open StructuralListFieldSyntax (field field_rename)

def selectedData {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G p : Fin m) : Formula m :=
  (field w S j p).conj (instanceAt Reln w z a A B f j N b L S D E p G)

theorem selectedData_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G p : Fin m)
    (ρ : Fin m → Fin l) :
    (selectedData Reln w z a A B f j N b L S D E G p).rename ρ =
      selectedData Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L)
        (ρ S) (ρ D) (ρ E) (ρ G) (ρ p) := by
  simp only [selectedData, Formula.rename, field_rename, instanceAt_rename]

def selected {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Formula m :=
  .ex (selectedData Reln w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc
    N.castSucc b.castSucc L.castSucc S.castSucc D.castSucc E.castSucc G.castSucc (Fin.last m))

theorem selected_rename {n m l} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m)
    (ρ : Fin m → Fin l) :
    (selected Reln w z a A B f j N b L S D E G).rename ρ =
      selected Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ L) (ρ S)
        (ρ D) (ρ E) (ρ G) := by
  simp only [selected, Formula.rename, selectedData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Use the actual condition image of slot j in the same mixed query. No
instance term, formula, guard result or proof output is supplied. -/
theorem from_condition_slot {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (n+2))
    (w z a A B f j N b L S D E G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hj : Derives Γ (.mem j f))
    (hG : Derives Γ (formulaCode w G z b)) (hp : Derives Γ (implication test w z b G E))
    (hq : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)) :
    Derives Γ (selected Reln w z a A B f j N b L S D E G) := by
  have hi := SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w L S a f z b D E hw (.conjR hq)
  have hf := Derives.conjR (Derives.conjL hi)
  have hjw := StructuralListTraceOrder.member_member hZ w j f hw (.conjL hf) hj
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc S.castSucc j.castSucc (Fin.last m))
  apply Derives.exE (p := P) (StructuralListFieldValues.exists_value hZ w S j hw hjw)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hf1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z b S Fin.castSucc) (under hf P)
  have ht := SyntaxMixedImageCodeFields.field_type w.castSucc f.castSucc z.castSucc b.castSucc S.castSucc
    j.castSucc (Fin.last m) hf1 (under hj P) (.conjR hP)
  have inst := from_query (ZFContext.under hZ P) Reln w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc
    f.castSucc j.castSucc N.castSucc b.castSucc L.castSucc S.castSucc D.castSucc E.castSucc (Fin.last m) G.castSucc
    (of_eq (omega_rename _ _) (under hw P)) (of_eq (empty_rename _ _) (under hz P)) ht
    (of_eq (formulaCode_rename _ _ _ _ _) (under hG P)) (of_eq (implication_rename _ _ _ _ _ _ _) (under hp P))
    (of_eq (ForcingDensityCode.queryData_rename Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _) (under hq P))
  simp only [Formula.raise, selected_rename]
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, selectedData_rename, Fin.lastCases_last,
    Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjR hP) inst)

def input {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((Formula.mem j f).conj ((formulaCode w G z b).conj
    ((implication test w z b G E).conj (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E)))))

def sentence {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) : Source.Sentence :=
  ((input Reln w z a A B f j N b L S D E G).imp (selected Reln w z a A B f j N b L S D E G)).close

theorem kernel_certificate {n m} (Reln : Source.Formula (n+2)) (w z a A B f j N b L S D E G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (sentence Reln w z a A B f j N b L S D E G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let P := input Reln w z a A B f j N b L S D E G
  have h : Derives (Context.add P (SetLanguage.ZF.at m)) P := .hyp (Or.inl rfl)
  have h2 := Derives.conjR h
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  exact from_condition_slot (ZFContext.add (ZFContext.source_ZF m) P) Reln w z a A B f j N b L S D E G
    (.conjL h) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) (.conjR h5)


/-- Read the complete point record of one actual density instance. Every
constructor, table, guard and tail remains an output of that instance. -/
private theorem with_opened_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S E p G M O Tail I X : Fin m)
    (ho : Derives Γ (opened w z a f b L S E p G M O Tail I X)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (o : Fin 5 → Fin l)
      (u v x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b)
        (o 1) (o 2) (o 3) (o 4)) →
      Derives Δ (ForcingRawModalBody.data (r w) (o 3) (o 4) (o 1) (r f) (o 2) (r b)
        (r M) (r O) (r Tail) (r I) (o 0) u) →
      Derives Δ (pointData (r w) (r z) (r b) (o 0) (r p) (r G) (u 1) (u 2) (u 3) (u 0) v) →
      Derives Δ (ForcingRawModalBody.data (r w) (v 2) (v 3) (v 0) (r b) (r z) (r b)
        (u 1) (u 2) (u 3) (u 0) (v 1) x) → Derives Δ (out.rename r)) : Derives Γ out := by
  refine eliminate_objects hZ 5 (fun t o => openedData (t w) (t z) (t a) (t f) (t b) (t L) (t S)
    (t E) (t p) (t G) (t M) (t O) (t Tail) (t I) (t X) o) ho out ?_
  intro l Δ r o hZ1 lift hOpened
  refine eliminate_objects hZ1 4 (fun s u => pointGuardsData (s (r w)) (s (r z)) (s (o 1))
    (s (r f)) (s (o 2)) (s (r b)) (s (o 3)) (s (o 4)) (s (o 0))
    (s (r p)) (s (r G)) (s (r M)) (s (r O)) (s (r Tail)) (s (r I)) u)
    (.conjR (.conjR (.conjR hOpened))) (out.rename r) ?_
  intro l1 Δ1 s u hZ2 move hGuards
  let e := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  have hLift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ s)
    (move (.conjL (.conjR hOpened)))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine eliminate_objects hZ2 4 (fun t v => pointData (t (e w)) (t (e z)) (t (e b)) (t (s (o 0)))
    (t (e p)) (t (e G)) (t (u 1)) (t (u 2)) (t (u 3)) (t (u 0)) v)
    (.conjR hGuards) (out.rename e) ?_
  intro l2 Δ2 t v hZ3 move2 hPoint
  let q := t ∘ e
  have carry2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename q) :=
    of_eq (SourceAlgebra.rename_comp F e t) (move2 (carry h))
  have hLift2 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ t) (move2 hLift)
  have hRaw2 := of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ u t) (move2 (.conjL hGuards))
  apply of_eq (SourceAlgebra.rename_comp out e t).symm
  refine eliminate_objects hZ3 4 (fun i x => ForcingRawModalBody.data (i (q w)) (i (v 2)) (i (v 3))
    (i (v 0)) (i (q b)) (i (q z)) (i (q b)) (i (t (u 1))) (i (t (u 2)))
    (i (t (u 3))) (i (t (u 0))) (i (v 1)) x)
    (.conjL (.conjR (.conjR hPoint))) (out.rename q) ?_
  intro l3 Δ3 i x hZ4 move3 hx
  let ρ := i ∘ q
  have carry3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F q i) (move3 (carry2 h))
  exact of_eq (SourceAlgebra.rename_comp out q i).symm
    (use ρ (i ∘ t ∘ s ∘ o) (i ∘ t ∘ u) (i ∘ v) x hZ4 carry3
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ i) (move3 hLift2))
      (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ (t ∘ u) i) (move3 hRaw2))
      (of_eq (pointData_rename _ _ _ _ _ _ _ _ _ _ v i) (move3 hPoint)) hx)

/-- Instantiate the actual outer universal at the supplied internal term,
retaining both guard queries and the original instance proof. -/
theorem with_outer_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f b L S D E p G M O Tail I X : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p)) (hG : Derives Γ (formulaCode w G z b))
    (hp : Derives Γ (implication test w z b G E))
    (hOuter : Derives Γ (ForcingRawModalBody.shell w D M O Tail I X))
    (hQ : Derives Γ (substituted w L S a f z b D E)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (o : Fin 5 → Fin l)
      (u v x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b)
        (o 1) (o 2) (o 3) (o 4)) →
      Derives Δ (ForcingRawModalBody.data (r w) (o 3) (o 4) (o 1) (r f) (o 2) (r b)
        (r M) (r O) (r Tail) (r I) (o 0) u) →
      Derives Δ (pointData (r w) (r z) (r b) (o 0) (r p) (r G) (u 1) (u 2) (u 3) (u 0) v) →
      Derives Δ (ForcingRawModalBody.data (r w) (v 2) (v 3) (v 0) (r b) (r z) (r b)
        (u 1) (u 2) (u 3) (u 0) (v 1) x) → Derives Δ (out.rename r)) : Derives Γ out :=
  with_opened_records hZ w z a f b L S E p G M O Tail I X
    (from_outer hZ w z a f b L S D E p G M O Tail I X hw hz ht hG hp hOuter hQ) out use

theorem with_instance_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (w z a A B f j N b L S D E p G : Fin m)
    (hi : Derives Γ (instanceAt Reln w z a A B f j N b L S D E p G))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l)
      (d : Fin 7 → Fin l) (s o : Fin 5 → Fin l) (u v x : Fin 4 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) d) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f)
        (d 2) (d 3) (d 4) (d 5) (d 6) (r D) s) →
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r L) (r S) (r a) (r f) (r z) (r b)
        (o 1) (o 2) (o 3) (o 4)) →
      Derives Δ (ForcingRawModalBody.data (r w) (o 3) (o 4) (o 1) (r f) (o 2) (r b)
        (d 2) (d 3) (s 2) (s 3) (o 0) u) →
      Derives Δ (pointData (r w) (r z) (r b) (o 0) (r p) (r G) (u 1) (u 2) (u 3) (u 0) v) →
      Derives Δ (ForcingRawModalBody.data (r w) (v 2) (v 3) (v 0) (r b) (r z) (r b)
        (u 1) (u 2) (u 3) (u 0) (v 1) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  refine eliminate_objects hZ 7 (fun r d => instanceData Reln (r w) (r z) (r a) (r A) (r B) (r f)
    (r j) (r N) (r b) (r L) (r S) (r D) (r E) (r p) (r G) d) hi out ?_
  intro l Δ r d hZ1 lift hd
  refine eliminate_objects hZ1 5 (fun s u => shellInstanceData (s (r w)) (s (r z)) (s (r a)) (s (r A)) (s (r B))
    (s (r f)) (s (r b)) (s (r L)) (s (r S)) (s (r D)) (s (r E)) (s (r p)) (s (r G))
    (s (d 2)) (s (d 3)) (s (d 4)) (s (d 5)) (s (d 6)) u) (.conjR hd) (out.rename r) ?_
  intro l1 Δ1 s u hZ2 lift1 hs
  let R := s ∘ r
  let ds := s ∘ d
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hData := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ d s) (lift1 (.conjL hd))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine with_opened_records hZ2 (R w) (R z) (R a) (R f) (R b) (R L) (R S)
    (R E) (R p) (R G) (ds 2) (ds 3) (u 2) (u 3) (u 4) (.conjR hs) (out.rename R) ?_
  intro l2 Δ2 t o y v x hZ3 lift2 hLift hRaw hPoint hx
  let q := t ∘ R
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename q) :=
    of_eq (SourceAlgebra.rename_comp F R t) (lift2 (move h))
  exact of_eq (SourceAlgebra.rename_comp out R t).symm
    (use q (t ∘ ds) (t ∘ u) o y v x hZ3 carry
      (of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ ds t) (lift2 hData))
      (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ u t) (lift2 (.conjL hs)))
      hLift hRaw hPoint hx)

open ForcingExistTailOpening (quantifiedData quantifiedData_rename quantified_output)
open ForcingRawModalBody (nestedData nestedData_rename nested_from_query)

section MixedShell

set_option maxHeartbeats 1200000

/-- The six original constructors, with the two outer guards followed by the
two inner guards and witness body in `leaf`. -/
def rawShell {m} (w D : Fin m) (leaf v : Fin 5 → Fin m) : Formula m :=
  (singleCode 9 w (v 4) D).conj
    ((binaryCode 2 w (leaf 0) (v 3) (v 4)).conj
      ((binaryCode 2 w (leaf 1) (v 2) (v 3)).conj
        ((singleCode 10 w (v 1) (v 2)).conj
          ((binaryCode 0 w (leaf 2) (v 0) (v 1)).conj (binaryCode 0 w (leaf 3) (leaf 4) (v 0))))))

theorem rawShell_rename {m l} (w D : Fin m) (leaf v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (rawShell w D leaf v).rename ρ = rawShell (ρ w) (ρ D) (ρ ∘ leaf) (ρ ∘ v) := by
  simp only [rawShell, Formula.rename, singleCode_rename, binaryCode_rename, Function.comp_apply]

theorem raw_of_shell {m} {Γ : Context m} (w a A B f D : Fin m) (leaf v : Fin 5 → Fin m)
    (h : Derives Γ (ForcingDensityCode.shellData w a A B f (leaf 0) (leaf 1) (leaf 2) (leaf 3) (leaf 4) D v)) :
    Derives Γ (rawShell w D leaf v) := by
  have h1 := Derives.conjR h
  have h2 := Derives.conjR h1
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  exact .conjI (.conjL (.conjR h4)) (.conjI (.conjL (.conjL h4))
    (.conjI (.conjL (.conjL h3)) (.conjI (.conjL (.conjL h2))
      (.conjI (.conjL (.conjL h1)) (.conjL (.conjL h))))))

/-- Once the five outputs agree, the actual two-binder codes agree. Both
traces may use independent object witnesses for every constructor. -/
theorem raw_shell_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w D E : Fin m) (leaf leaf' v v' : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hLeaf : ∀ i, Derives Γ (.equal (leaf i) (leaf' i)))
    (hD : Derives Γ (rawShell w D leaf v)) (hE : Derives Γ (rawShell w E leaf' v')) :
    Derives Γ (.equal D E) := by
  have unary (tag : Nat) (x y p q : Fin m) (hxy : Derives Γ (.equal x y))
      (hp : Derives Γ (singleCode tag w x p)) (hq : Derives Γ (singleCode tag w y q)) :
      Derives Γ (.equal p q) :=
    SyntaxLogicalFields.single_unique hZ tag w y p q hw
      (ProjectCompilerUniqueTransport.single_input tag w x p y hxy hp) hq
  have binary (kind : Fin 4) (x y x' y' p q : Fin m)
      (hx : Derives Γ (.equal x x')) (hy : Derives Γ (.equal y y'))
      (hp : Derives Γ (binaryCode kind w x y p)) (hq : Derives Γ (binaryCode kind w x' y' q)) :
      Derives Γ (.equal p q) :=
    SyntaxLogicalFields.binary_unique hZ kind w x' y' p q hw
      (ProjectCompilerUniqueTransport.binary_right kind w x' y p y' hy
        (ProjectCompilerUniqueTransport.binary_left kind w x y p x' hx hp)) hq
  have hD1 := Derives.conjR hD
  have hE1 := Derives.conjR hE
  have hD2 := Derives.conjR hD1
  have hE2 := Derives.conjR hE1
  have hD3 := Derives.conjR hD2
  have hE3 := Derives.conjR hE2
  have hD4 := Derives.conjR hD3
  have hE4 := Derives.conjR hE3
  have e0 := binary 0 _ _ _ _ _ _ (hLeaf 3) (hLeaf 4) (.conjR hD4) (.conjR hE4)
  have e1 := binary 0 _ _ _ _ _ _ (hLeaf 2) e0 (.conjL hD4) (.conjL hE4)
  have e2 := unary 10 _ _ _ _ e1 (.conjL hD3) (.conjL hE3)
  have e3 := binary 2 _ _ _ _ _ _ (hLeaf 1) e2 (.conjL hD2) (.conjL hE2)
  have e4 := binary 2 _ _ _ _ _ _ (hLeaf 0) e3 (.conjL hD1) (.conjL hE1)
  exact unary 9 _ _ _ _ e4 (.conjL hD) (.conjL hE)

def mixedLeaves {m} (x y : Fin 4 → Fin m) : Fin 5 → Fin m :=
  Fin.cases (x 1) (Fin.cases (x 2) (Fin.cases (y 1) (Fin.cases (y 2) (fun _ => y 3))))

def mixedNodes {m} (u t : Fin 5 → Fin m) (x y : Fin 4 → Fin m) : Fin 5 → Fin m :=
  Fin.cases (y 0) (Fin.cases (t 0) (Fin.cases (x 3) (Fin.cases (x 0) (fun _ => u 0))))

/-- Read the actual substituted density formula under both condition binders.
The outer guards use one lift of the original lists, and the inner guards and
atomic witness use the second lift of those same lists. -/
theorem with_mixed_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w L S a f c b D E : Fin m) (leaf v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (rawShell w D leaf v))
    (hq : Derives Γ (substituted w L S a f c b D E)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (u t : Fin 5 → Fin l) (x y : Fin 4 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (quantifiedData true (r w) (r L) (r S) (r a) (r f) (r c) (r b) (r (v 4)) (r E) u) →
      Derives Δ (nestedData 2 (r w) (u 3) (u 4) (u 1) (r f) (u 2) (r b)
        (r (leaf 0)) (r (leaf 1)) (r (v 2)) (r (v 3)) (u 0) x) →
      Derives Δ (quantifiedData false (r w) (u 3) (u 4) (u 1) (r f) (u 2) (r b) (r (v 1)) (x 3) t) →
      Derives Δ (nestedData 0 (r w) (t 3) (t 4) (t 1) (r f) (t 2) (r b)
        (r (leaf 2)) (r (leaf 3)) (r (leaf 4)) (r (v 0)) (t 0) y) →
      Derives Δ (rawShell (r w) (r E) (mixedLeaves x y) (mixedNodes u t x y)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hOuter := quantified_output hZ true w L S a f c b D (v 4) E hw (.conjL hs) hq
  refine eliminate_objects hZ 5 (fun r u => quantifiedData true
    (r w) (r L) (r S) (r a) (r f) (r c) (r b) (r (v 4)) (r E) u) hOuter out ?_
  intro l Δ r u hZ1 lift hu
  have hs1 := of_eq (rawShell_rename w D leaf v r) (lift hs)
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hImps := nested_from_query hZ1 2 (r w) (u 3) (u 4) (u 1) (r f) (u 2) (r b)
    (r (leaf 0)) (r (leaf 1)) (r (v 2)) (r (v 3)) (r (v 4)) (u 0) hw1
    (.conjL (.conjR hs1)) (.conjL (.conjR (.conjR hs1))) (.conjR (.conjR hu))
  refine eliminate_objects hZ1 4 (fun s x => nestedData 2 (s (r w)) (s (u 3)) (s (u 4))
    (s (u 1)) (s (r f)) (s (u 2)) (s (r b)) (s (r (leaf 0))) (s (r (leaf 1)))
    (s (r (v 2))) (s (r (v 3))) (s (u 0)) x) hImps (out.rename r) ?_
  intro l1 Δ1 s x hZ2 lift1 hx
  let R := s ∘ r
  let U := s ∘ u
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hs2 := of_eq (rawShell_rename w D leaf v R) (carry hs)
  have hw2 := of_eq (omega_rename w R) (carry hw)
  have hu2 := of_eq (quantifiedData_rename true (r w) (r L) (r S) (r a) (r f) (r c) (r b)
    (r (v 4)) (r E) u s) (lift1 hu)
  have hInner := quantified_output hZ2 false (R w) (U 3) (U 4) (U 1) (R f) (U 2) (R b)
    (R (v 2)) (R (v 1)) (x 3) hw2 (.conjL (.conjR (.conjR (.conjR hs2))))
    (.conjR (.conjR (.conjR hx)))
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 5 (fun e t => quantifiedData false (e (R w)) (e (U 3)) (e (U 4))
    (e (U 1)) (e (R f)) (e (U 2)) (e (R b)) (e (R (v 1))) (e (x 3)) t) hInner (out.rename R) ?_
  intro l2 Δ2 e t hZ3 lift2 ht
  let Q := e ∘ R
  let V := e ∘ U
  let X := e ∘ x
  have carry2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename Q) :=
    of_eq (SourceAlgebra.rename_comp F R e) (lift2 (carry h))
  have hs3 := of_eq (rawShell_rename w D leaf v Q) (carry2 hs)
  have hw3 := of_eq (omega_rename w Q) (carry2 hw)
  have hu3 := of_eq (quantifiedData_rename true (R w) (R L) (R S) (R a) (R f) (R c) (R b)
    (R (v 4)) (R E) U e) (lift2 hu2)
  have hx3 := of_eq (nestedData_rename 2 (R w) (U 3) (U 4) (U 1) (R f) (U 2) (R b)
    (R (leaf 0)) (R (leaf 1)) (R (v 2)) (R (v 3)) (U 0) x e) (lift2 hx)
  have hAnds := nested_from_query hZ3 0 (Q w) (t 3) (t 4) (t 1) (Q f) (t 2) (Q b)
    (Q (leaf 2)) (Q (leaf 3)) (Q (leaf 4)) (Q (v 0)) (Q (v 1)) (t 0) hw3
    (.conjL (.conjR (.conjR (.conjR (.conjR hs3)))))
    (.conjR (.conjR (.conjR (.conjR (.conjR hs3))))) (.conjR (.conjR ht))
  refine of_eq (SourceAlgebra.rename_comp out R e).symm ?_
  refine eliminate_objects hZ3 4 (fun j y => nestedData 0 (j (Q w)) (j (t 3)) (j (t 4))
    (j (t 1)) (j (Q f)) (j (t 2)) (j (Q b)) (j (Q (leaf 2))) (j (Q (leaf 3)))
    (j (Q (leaf 4))) (j (Q (v 0))) (j (t 0)) y) hAnds (out.rename Q) ?_
  intro l3 Δ3 j y hZ4 lift3 hy
  let T := j ∘ Q
  have carry3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename T) :=
    of_eq (SourceAlgebra.rename_comp F Q j) (lift3 (carry2 h))
  have hU := of_eq (quantifiedData_rename true _ _ _ _ _ _ _ _ _ V j) (lift3 hu3)
  have hX := of_eq (nestedData_rename 2 _ _ _ _ _ _ _ _ _ _ _ _ X j) (lift3 hx3)
  have hT := of_eq (quantifiedData_rename false _ _ _ _ _ _ _ _ _ t j) (lift3 ht)
  have target : Derives Δ3 (rawShell (T w) (T E) (mixedLeaves (j ∘ X) y)
      (mixedNodes (j ∘ V) (j ∘ t) (j ∘ X) y)) :=
    .conjI (.conjL hU) (.conjI (.conjL (.conjL hX)) (.conjI (.conjL (.conjR hX))
      (.conjI (.conjL hT) (.conjI (.conjL (.conjL hy)) (.conjL (.conjR hy))))))
  exact of_eq (SourceAlgebra.rename_comp out Q j).symm
    (use T (j ∘ V) (j ∘ t) (j ∘ X) y hZ4 carry3 hU hX hT hy target)

end MixedShell

private theorem weaken_bound_value {m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f N W x u i I : Fin m) (v : Fin 3 → Fin m)
    (hw : Source.Derives Γ (omega w))
    (hwk : Source.Derives Γ (ForcingDensityCode.weakenData w a A f N W v))
    (hi : Source.Derives Γ (.mem i a)) (hs : Source.Derives Γ (successor I i))
    (hx : Source.Derives Γ (SyntaxVariableSyntax.code true w i x))
    (h0 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (v 1) (v 2) a f A f x u)) :
    Source.Derives Γ (SyntaxVariableSyntax.code true w I u) := by
  have hl := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w (v 1) (v 2) a f A f x u h0)
  have hField := Source.Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w
    (v 1) (v 2) a f A f x u i hw hl hx)) h0
  have hEdge := Source.Derives.impE (.conjR (SyntaxMixedImageCodeFields.edges w (v 0) a A f (v 1) i u (.conjL (.conjR hwk)))) hField
  exact .impE (.conjL (SyntaxVariableTableFields.shifted_at hZ true w a A f (v 0) i I u (.conjL hwk) hi hs)) hEdge

private theorem weakening_term_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f c b L U E N W x x' y o : Fin m) (v : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hWeak : Derives Γ (ForcingDensityCode.weakenData w a A f N W v))
    (shift : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (i I o : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (.mem i (r w)) → Derives Δ (.mem i (r a)) → Derives Δ (successor I i) →
      Derives Δ (field (r w) (r L) i o) → Derives Δ (field (r w) (r U) I o))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w a f A c b (v 1) (v 2) U E L E x x' y o)) :
    Derives Γ (.equal y o) := by
  apply OriginalTermScopeElimination.eliminate w a f x (.equal y o)
    (SyntaxCodedMixedTermTyping.source_type w (v 1) (v 2) a f A f x x' (.conjL hPath))
  intro bound
  let i := Fin.last m
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let B := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a f) x
  let Δ := Source.Context.add B (Source.Context.image Source.Formula.raise Γ)
  have hB : Source.Derives Δ B := .hyp (Or.inl rfl)
  have lift {G : Source.Formula m} (h : Source.Derives Γ G) : Source.Derives Δ (G.rename r) := SourceLogic.under h B
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hp := of_eq (ForcingRelationImages.guardPath_rename w a f A c b (v 1) (v 2) U E L E x x' y o r) (lift hPath)
  have p0 := Source.Derives.conjL hp
  have p1 := Source.Derives.conjL (.conjR hp)
  have p2 := Source.Derives.conjR (.conjR hp)
  have hL0 := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted
    (r w) (r (v 1)) (r (v 2)) (r a) (r f) (r A) (r f) (r x) (r x') p0)
  have hL1 := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted
    (r w) (r U) (r E) (r A) (r f) (r c) (r b) (r x') (r y) p1)
  have hL2 := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted
    (r w) (r L) (r E) (r a) (r f) (r c) (r b) (r x) (r o) p2)
  have hO := Source.Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 bound
    (r w) (r L) (r E) (r a) (r f) (r c) (r b) (r x) (r o) i hw1 hL2 (.conjR hB))) p2
  have hWeak1 := of_eq (ForcingDensityCode.weakenData_rename w a A f N W v r) (lift hWeak)
  cases bound with
  | false =>
    have hf := Source.Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false
      (r w) (r (v 1)) (r (v 2)) (r a) (r f) (r A) (r f) (r x) (r x') i hw1 hL0 (.conjR hB))) p0
    have hX := ForcingMemberGuard.identity_field hZ1 (r w) (r A) (r f) (r (v 2)) i (r x')
      (.conjL (.conjR (.conjR hWeak1))) (.conjL hf) (.conjR hf)
    have hy := Source.Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false
      (r w) (r U) (r E) (r A) (r f) (r c) (r b) (r x') (r y) i hw1 hL1 hX)) p1
    have hiW := StructuralListTraceOrder.member_member hZ1 (r w) i (r f) hw1 (.conjL (.conjR hL2)) (.conjL hO)
    exact StructuralListFieldValues.unique hZ1 (r w) (r E) i (r y) (r o) hw1 hiW (.conjR hy) (.conjR hO)
  | true =>
    let out := Source.Formula.equal (r y) (r o)
    have hI := InsertExistence.exists_insert i i (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
    refine eliminate_objects hZ1 1 (fun s vs => successor (vs 0) (s i)) hI out ?_
    intro l Ξ s vs hZ2 move hs
    let I := vs 0
    let p := s ∘ r
    let i' := s i
    have carry {G : Source.Formula m} (h : Source.Derives Γ G) : Source.Derives Ξ (G.rename p) :=
      of_eq (SourceAlgebra.rename_comp G r s) (move (lift h))
    have hw2 := of_eq (omega_rename w p) (carry hw)
    have hW := of_eq (ForcingDensityCode.weakenData_rename w a A f N W v p) (carry hWeak)
    have ho := of_eq (field_rename (r w) (r L) i (r o) s) (move (.conjR hO))
    have hX := weaken_bound_value hZ2 (p w) (p a) (p A) (p f) (p N) (p W) (p x) (p x') i' I (p ∘ v)
      hw2 hW (move (.conjL hO)) hs
      (of_eq (SyntaxVariableSyntax.code_rename true (r w) i (r x) s) (move (.conjR hB)))
      (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename (r w) (r (v 1)) (r (v 2))
        (r a) (r f) (r A) (r f) (r x) (r x') s) (move p0))
    have hY := Source.Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 true
      (p w) (p U) (p E) (p A) (p f) (p c) (p b) (p x') (p y) I hw2
      (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename (r w) (r A) (r f) (r c) (r b) (r U) (r E) s)
        (move hL1)) hX))
      (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename (r w) (r U) (r E) (r A) (r f) (r c) (r b)
        (r x') (r y) s) (move p1))
    have hiw := SyntaxVariableDecode.index_natural true (p w) i' (p x)
      (of_eq (SyntaxVariableSyntax.code_rename true (r w) i (r x) s) (move (.conjR hB)))
    have hOld := shift p i' I (p o) hZ2 carry hiw (move (.conjL hO)) hs ho
    have hIw := SyntaxVariableDecode.index_natural true (p w) I (p x') hX
    exact StructuralListFieldValues.unique hZ2 (p w) (p U) I (p y) (p o) hw2 hIw (.conjR hY) hOld

/-- Cancel the original density weakening against a table that reads each old
bound field at its successor index. The original free images are unchanged. -/
theorem direct_after_weakening {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f c b L U E N W Y : Fin m) (v : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a c b L))
    (hWeak : Derives Γ (ForcingDensityCode.weakenData w a A f N W v))
    (hRun : Derives Γ (substituted w U E A f c b W Y))
    (shift : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (i I o : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (.mem i (r w)) → Derives Δ (.mem i (r a)) → Derives Δ (successor I i) →
      Derives Δ (field (r w) (r L) i o) → Derives Δ (field (r w) (r U) I o)) :
    Derives Γ (substituted w L E a f c b N Y) := by
  have hInput := SyntaxMixedFormulaOutput.input_of_substituted hZ w U E A f c b W Y hw hRun
  have hE := Derives.conjR (.conjR hInput)
  apply ForcingRelationGuardFormula.to_direct_at_scope hZ w a f A c b (v 1) (v 2) U E L E N W Y
    hw (.conjL hL) (.conjL hE) hL hE (.conjR (.conjR (.conjR hWeak))) hRun
  intro l Δ r hZ1 move x x' y o hPath
  exact weakening_term_agreement hZ1 (r w) (r a) (r A) (r f) (r c) (r b) (r L) (r U) (r E)
    (r N) (r W) x x' y o (r ∘ v) (of_eq (omega_rename w r) (move hw))
    (of_eq (ForcingDensityCode.weakenData_rename w a A f N W v r) (move hWeak))
    (fun s i I o hZ2 move2 hiw hi hs ho =>
      shift (s ∘ r) i I o hZ2 (fun hp => of_eq (SourceAlgebra.rename_comp _ r s) (move2 (move hp))) hiw hi hs ho)
    hPath

/-- Open the actual density proof at the same fresh term and image tables
used to open a modal parent. The guarded existential remains its exact output. -/
theorem with_fresh_instance_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N b c d t L S D E G W : Fin m) (images : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hc : Derives Γ (successor c z)) (hd : Derives Γ (successor d b))
    (hCode : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z d t))
    (hImages : Derives Γ (ForcingWeakenedImages.data w a f z b d L S images))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 7 → Fin l) (s : Fin 5 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f) (v 2) (v 3) (v 4) (v 5) (v 6) (r D) s) →
      Derives Δ (ForcingFreshParentOpening.data (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
        (r L) (r S) (r D) (s 4) (r E) (r ∘ images) u) →
      Derives Δ (ForcingRawModalBody.nestedData 2 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
        (v 2) (v 3) (s 2) (s 3) (u 8) x) →
      Derives Δ (implication test (r w) (r z) (r d) (r W) (u 8)) →
      Derives Δ (out.rename r)) :
    Derives Γ out := by
  refine eliminate_objects hZ 7 (fun r v => ForcingDensityCode.data Reln (r w) (r a) (r A) (r B)
    (r f) (r j) (r N) (r D) v) hCompiled out ?_
  intro l Δ r v hZ1 move hData
  have hShell := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hData)))))
  refine eliminate_objects hZ1 5 (fun s ys => ForcingDensityCode.shellData (s (r w)) (s (r a)) (s (r A)) (s (r B))
    (s (r f)) (s (v 2)) (s (v 3)) (s (v 4)) (s (v 5)) (s (v 6)) (s (r D)) ys) hShell (out.rename r) ?_
  intro l' Ξ s nodes hZ2 move2 hS
  let p := s ∘ r
  let M := s (v 2)
  let O := s (v 3)
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename p) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move2 (move h))
  have hS4 := Derives.conjR (.conjR (.conjR hS))
  have hS5 := Derives.conjR hS4
  have hIn : Derives Ξ (ForcingFreshParentOpening.input (p w) (p z) (p a) (p f) (p A) (p b)
      (p c) (p d) (p t) (p L) (p S) (p D) (nodes 4) (p E)) :=
    .conjI (of_eq (omega_rename w p) (carry hw)) (.conjI (of_eq (empty_rename z p) (carry hz))
      (.conjI (of_eq (successor_rename A a p) (carry hA)) (.conjI (of_eq (successor_rename c z p) (carry hc))
        (.conjI (of_eq (successor_rename d b p) (carry hd))
          (.conjI (of_eq (SyntaxVariableSyntax.code_rename false w z t p) (carry hCode))
            (.conjI (of_eq (SyntaxTermSyntax.term_rename w z d t p) (carry ht))
              (.conjI (.conjL (.conjR hS5)) (of_eq (substituted_rename w L S a f z b D E p) (carry hQuery)))))))))
  have hOpen := ForcingFreshParentOpening.produce_at_images hZ2 (p w) (p z) (p a) (p f) (p A) (p b)
    (p c) (p d) (p t) (p L) (p S) (p D) (nodes 4) (p E) (p ∘ images) hIn
    (of_eq (ForcingWeakenedImages.data_rename w a f z b d L S images p) (carry hImages))
  refine eliminate_objects hZ2 9 (fun q u => ForcingFreshParentOpening.data (q (p w)) (q (p z)) (q (p a))
    (q (p f)) (q (p A)) (q (p b)) (q (p c)) (q (p d)) (q (p t)) (q (p L)) (q (p S)) (q (p D)) (q (nodes 4)) (q (p E))
    (q ∘ p ∘ images) u) hOpen ((out.rename r).rename s) ?_
  intro l'' Ω q u hZ3 move3 hU
  let e := q ∘ p
  have carry2 {F : Formula m} (h : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F p q) (move3 (carry h))
  have hW := ForcingOldParentInstance.from_opened hZ3 test (e w) (e z) (e a) (e f) (e A) (e b)
    (e c) (e d) (e t) (e L) (e S) (e D) (q (nodes 4)) (e E) (e G) (e W) (e ∘ images) u hU
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename w z b d G W e) (carry2 hWeakG))
    (of_eq (implication_rename test w z b G E e) (carry2 hProof))
  have hU8 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hU)))))))
  have hNested := ForcingRawModalBody.nested_from_query hZ3 2 (e w) (u 7) (e (images 9)) (e A) (e f) (e z) (e d)
    (q M) (q O) (q (nodes 2)) (q (nodes 3)) (q (nodes 4)) (u 8)
    (of_eq (omega_rename w e) (carry2 hw))
    (of_eq (binaryCode_rename 2 (p w) M (nodes 3) (nodes 4) q) (move3 (.conjL (.conjL hS5))))
    (of_eq (binaryCode_rename 2 (p w) O (nodes 2) (nodes 3) q) (move3 (.conjL (.conjL hS4))))
    (.conjL hU8)
  refine eliminate_objects hZ3 4 (fun h x => ForcingRawModalBody.nestedData 2 (h (e w)) (h (u 7)) (h (e (images 9)))
    (h (e A)) (h (e f)) (h (e z)) (h (e d)) (h (q M)) (h (q O)) (h (q (nodes 2))) (h (q (nodes 3))) (h (u 8)) x)
    hNested (((out.rename r).rename s).rename q) ?_
  intro l''' Θ h x hZ4 move4 hX
  let r' := h ∘ q ∘ s
  let e' := r' ∘ r
  have carry1 {F : Formula l} (d : Derives Δ F) : Derives Θ (F.rename r') :=
    of_eq ((SourceAlgebra.rename_comp (F.rename s) q h).trans (SourceAlgebra.rename_comp F s (h ∘ q)))
      (move4 (move3 (move2 d)))
  have carry0 {F : Formula m} (d : Derives Γ F) : Derives Θ (F.rename e') :=
    of_eq (SourceAlgebra.rename_comp F r r') (carry1 (move d))
  have hData' := of_eq (ForcingDensityCode.data_rename Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v r')
    (carry1 hData)
  have hS' := of_eq (ForcingDensityCode.shellData_rename (p w) (p a) (p A) (p B) (p f) M O (s (v 4)) (s (v 5))
    (s (v 6)) (p D) nodes (h ∘ q))
    (of_eq (SourceAlgebra.rename_comp _ q h) (move4 (move3 hS)))
  have hU' := of_eq (ForcingFreshParentOpening.data_rename (e w) (e z) (e a) (e f) (e A) (e b) (e c) (e d)
    (e t) (e L) (e S) (e D) (q (nodes 4)) (e E) (e ∘ images) u h) (move4 hU)
  have hP' := of_eq (implication_rename test (e w) (e z) (e d) (e W) (u 8) h) (move4 hW)
  exact of_eq ((SourceAlgebra.rename_comp ((out.rename r).rename s) q h).trans
    ((SourceAlgebra.rename_comp (out.rename r) s (h ∘ q)).trans (SourceAlgebra.rename_comp out r r'))).symm
    (use e' (r' ∘ v) (h ∘ q ∘ nodes) (h ∘ u) x hZ4 carry0 hData' hS' hU' hX hP')

private theorem with_opened_density_tail {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N b c d t L S D E G W H body Parent
      headZero head Member Order Tail Inner : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (outputs : Fin 4 → Fin m)
    (hParent : Derives Γ (ForcingFreshParentOpening.data w z a f A b c d t L S N body Parent images opened))
    (hZero : Derives Γ (empty headZero))
    (hHeadCode : Derives Γ (SyntaxVariableSyntax.code true w headZero head))
    (hMember : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Member))
    (hOrder : Derives Γ (ForcingGuardCode.compiled true Reln w A f head Order))
    (hOpenedQueries : Derives Γ (ForcingRawModalBody.data w (opened 7) (images 9) A f z d
      Member Order Tail Inner (opened 8) outputs))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (hM : Derives Γ (implication test w z d H (outputs 1)))
    (hO : Derives Γ (implication test w z d H (outputs 2)))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 7 → Fin l) (s : Fin 5 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (.equal (r (opened 7)) (u 7)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f) (v 2) (v 3) (v 4) (v 5) (v 6) (r D) s) →
      Derives Δ (ForcingFreshParentOpening.data (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
        (r L) (r S) (r D) (s 4) (r E) (r ∘ images) u) →
      Derives Δ (ForcingRawModalBody.nestedData 2 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
        (v 2) (v 3) (s 2) (s 3) (u 8) x) →
      Derives Δ (implication test (r w) (r z) (r d) (r H) (x 3)) →
      Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hIn := Derives.conjL hParent
  have hw := Derives.conjL hIn
  have hz := Derives.conjL (.conjR hIn)
  have hIn2 := Derives.conjR (.conjR hIn)
  have hIn3 := Derives.conjR hIn2
  have hIn4 := Derives.conjR hIn3
  have hIn5 := Derives.conjR hIn4
  have ht := Derives.conjL (.conjR hIn5)
  refine with_fresh_instance_records hZ Reln w z a A B f j N b c d t L S D E G W images
    hw hz (.conjL hIn2) (.conjL hIn3) (.conjL hIn4) (.conjL hIn5) ht
    (.conjL (.conjR hParent)) hCompiled hQuery hWeakG hProof out ?_
  intro l Δ r v s u x hZ1 move hDensity hShell hOpen hQueryOut hp
  have hw1 := of_eq (omega_rename w r) (move hw)
  have hz1 := of_eq (empty_rename z r) (move hz)
  have hOld := of_eq (ForcingFreshParentOpening.data_rename w z a f A b c d t L S N body Parent images opened r) (move hParent)
  have hOldRun := of_eq (ForcingRawModalBody.data_rename w (opened 7) (images 9) A f z d
    Member Order Tail Inner (opened 8) outputs r) (move hOpenedQueries)
  have hNewHead := Derives.conjL hDensity
  have eEmpty := OmegaUniversal.empty_unique (r headZero) (v 0) (ZFContext.arithmetic hZ1).base.extensionality
    (of_eq (empty_rename _ _) (move hZero)) (.conjL hNewHead)
  have hHead := SyntaxVariableImagePoint.code_subst_index true (r w) (r headZero) (r head) (v 0)
    eEmpty (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ r) (move hHeadCode))
  have eHead := SyntaxVariables.unique hZ1 true (r w) (v 0) (r head) (v 1) hw1 hHead (.conjL (.conjR hNewHead))
  have hOldCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOld)))))))
  have hNewCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists (r w) (r (images 8)) (r (images 9)) (r a) (r f)
    (r z) (r d) (r A) (r c) (u 2) (u 3) hLift
  have hList := Derives.conjL hLists
  have ht1 := SyntaxTerms.range hZ1 (r w) (r z) (r d) (r t) hw1 (of_eq (SyntaxTermSyntax.term_rename w z d t r) (move ht))
  have eList := StructuralConsUnique.unique hZ1 (r w) (r t) (r (images 8)) (r (opened 7)) (u 7) hw1 ht1
    (.conjL (.conjL (.conjR (.conjR hList)))) hOldCons hNewCons
  have compare (order : Bool) (M O Y Y' : Fin l)
      (hm : Derives Δ (ForcingGuardCode.compiled order Reln (r w) (r A) (r f) (r head) M))
      (ho : Derives Δ (ForcingGuardCode.compiled order Reln (r w) (r A) (r f) (v 1) O))
      (hY : Derives Δ (substituted (r w) (r (opened 7)) (r (images 9)) (r A) (r f) (r z) (r d) M Y))
      (hY' : Derives Δ (substituted (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) O Y')) :
      Derives Δ (.equal Y Y') := by
    let P := ForcingGuardCode.compiled order Reln (r w).castSucc (r A).castSucc (r f).castSucc (Fin.last l) M.castSucc
    have inst (i : Fin l) : P.instantiate i = ForcingGuardCode.compiled order Reln (r w) (r A) (r f) i M := by
      simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    have hm' := of_eq (inst (v 1)) (.eqSubst P eHead (of_eq (inst (r head)).symm hm))
    have eq := ForcingGuardCode.unique hZ1 order Reln (r w) (r A) (r f) (v 1) M O hw1 hm' ho
    have hY1 := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (opened 7)) (r (images 9))
      (r A) (r f) (r z) (r d) M Y (u 7) eList hY
    exact SyntaxMixedFormulaOutputInduction.unique hZ1 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) O Y Y'
      hw1 (SyntaxMixedFormulaJudgmentSubst.subst_n (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) M Y O eq hY1) hY'
  have eM := compare false (r Member) (v 2) (r (outputs 1)) (x 1)
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ r) (move hMember)) (.conjL (.conjR hDensity))
    (.conjL (.conjR (.conjL hOldRun))) (.conjL (.conjR (.conjL hQueryOut)))
  have eO := compare true (r Order) (v 3) (r (outputs 2)) (x 2)
    (of_eq (ForcingGuardCode.compiled_rename true Reln _ _ _ _ _ r) (move hOrder)) (.conjL (.conjR (.conjR hDensity)))
    (.conjL (.conjR (.conjR hOldRun))) (.conjL (.conjR (.conjR hQueryOut)))
  have hOuter := ProjectCompilerUniqueTransport.binary_left 2 (r w) (x 1) (x 0) (u 8) (r (outputs 1))
    (eq_symm eM) (.conjL (.conjL hQueryOut))
  have hInner := ProjectCompilerUniqueTransport.binary_left 2 (r w) (x 2) (x 3) (x 0) (r (outputs 2))
    (eq_symm eO) (.conjL (.conjR hQueryOut))
  have hOuterType := SyntaxMixedFormulaJudgment.target_type (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
    (s 4) (u 8) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))))
  have hInnerType := SyntaxMixedFormulaJudgment.target_type (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
    (s 3) (x 0) (.conjR (.conjR (.conjL hQueryOut)))
  have hH1 := of_eq (formulaCode_rename w H z d r) (move hH)
  have hY := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) (r H) (r W) (u 8) hw1 hz1 hH1
    (of_eq (formulaCode_rename w W z d r) (move hW)) hOuterType
    (of_eq (implication_rename test w z d H W r) (move hToW)) hp
  have hI := ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r d) (r H) (r (outputs 1)) (x 0) (u 8)
    hw1 hz1 hH1 hOuterType hOuter (of_eq (implication_rename test w z d H (outputs 1) r) (move hM)) hY
  have hTail := ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r d) (r H) (r (outputs 2)) (x 3) (x 0)
    hw1 hz1 hH1 hInnerType hInner (of_eq (implication_rename test w z d H (outputs 2) r) (move hO)) hI
  exact use r v s u x hZ1 move eList hDensity hShell hOpen hQueryOut hTail

/-- At the actual opened negative condition, the two density guards are the
same original guard queries. Discharge them under the current internal proof
background and retain the density existential and its actual records. -/
theorem with_negative_density_tail {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N C b c d t L S D E G W H body Parent : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (negData : Fin 5 → Fin m)
    (negNodes negOut : Fin 4 → Fin m)
    (hNeg : Derives Γ (ForcingRawModalBody.negativeRecord Reln w z a f A b c d t L S j C N body Parent
      images negOpen negData negNodes))
    (hNegQueries : Derives Γ (ForcingRawModalBody.data w (negOpen 7) (images 9) A f z d
      (negData 3) (negData 4) (negNodes 1) (negNodes 2) (negOpen 8) negOut))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (hM : Derives Γ (implication test w z d H (negOut 1)))
    (hO : Derives Γ (implication test w z d H (negOut 2)))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 7 → Fin l) (s : Fin 5 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (.equal (r (negOpen 7)) (u 7)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f) (v 2) (v 3) (v 4) (v 5) (v 6) (r D) s) →
      Derives Δ (ForcingFreshParentOpening.data (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
        (r L) (r S) (r D) (s 4) (r E) (r ∘ images) u) →
      Derives Δ (ForcingRawModalBody.nestedData 2 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
        (v 2) (v 3) (s 2) (s 3) (u 8) x) →
      Derives Δ (implication test (r w) (r z) (r d) (r H) (x 3)) →
      Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hCompiler := Derives.conjL (.conjR hNeg)
  have hHead := Derives.conjL hCompiler
  exact with_opened_density_tail hZ Reln w z a A B f j N b c d t L S D E G W H body Parent
    (negData 0) (negData 1) (negData 3) (negData 4) (negNodes 1) (negNodes 2)
    images negOpen negOut (.conjL hNeg) (.conjL hHead) (.conjL (.conjR hHead))
    (.conjL (.conjR (.conjR hCompiler))) (.conjL (.conjR (.conjR (.conjR hCompiler))))
    hNegQueries hCompiled hQuery hWeakG hProof hH hW hToW hM hO out use

-- Open a literal EX at the given fresh term using the existing image tables.
theorem with_fresh_existential_body_at_images {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B f b c d t L S Tail Body E rM rO N Rest : Fin m) (images : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hc : Derives Γ (successor c z)) (hd : Derives Γ (successor d b))
    (hCode : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z d t))
    (hBinder : Derives Γ (singleCode 10 w Body Tail))
    (hOuter : Derives Γ (binaryCode 0 w rM Rest Body))
    (hInner : Derives Γ (binaryCode 0 w rO N Rest))
    (hQuery : Derives Γ (substituted w L S A f z b Tail E))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S images))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (r w) (r z) (r A) (r f) (r B) (r b) (r c) (r d) (r t)
        (r L) (r S) (r Tail) (r Body) (r E) (r ∘ images) u) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (r w) (u 7) (r (images 9)) (r B) (r f) (r z) (r d)
        (r rM) (r rO) (r N) (r Rest) (u 8) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hIn : Derives Γ (ForcingFreshParentOpening.quantifiedInput false w z A f B b c d t L S Tail Body E) :=
    .conjI hw (.conjI hz (.conjI hB (.conjI hc (.conjI hd (.conjI hCode (.conjI ht
      (.conjI hBinder hQuery)))))))
  have he := ForcingFreshParentOpening.produce_quantified_at_images hZ false w z A f B b c d t
    L S Tail Body E images hIn hImages
  refine eliminate_objects hZ 9 (fun p u => ForcingFreshParentOpening.quantifiedData false
    (p w) (p z) (p A) (p f) (p B) (p b) (p c) (p d) (p t) (p L) (p S) (p Tail) (p Body) (p E)
    (p ∘ images) u) he out ?_
  intro l Ξ p u hZ2 carry hOpen
  have hU8 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen))))))))
  have hNested := ForcingRawModalBody.nested_from_query hZ2 0 (p w) (u 7) (p (images 9)) (p B) (p f) (p z) (p d)
    (p rM) (p rO) (p N) (p Rest) (p Body) (u 8)
    (of_eq (omega_rename w p) (carry hw)) (of_eq (binaryCode_rename 0 _ _ _ _ p) (carry hOuter))
    (of_eq (binaryCode_rename 0 _ _ _ _ p) (carry hInner)) hU8
  refine eliminate_objects hZ2 4 (fun q x => ForcingRawModalBody.nestedData 0 (q (p w)) (q (u 7)) (q (p (images 9)))
    (q (p B)) (q (p f)) (q (p z)) (q (p d)) (q (p rM)) (q (p rO)) (q (p N)) (q (p Rest)) (q (u 8)) x)
    hNested (out.rename p) ?_
  intro l'' Ω q x hZ3 move3 hWitness
  let e := q ∘ p
  have carry0 {F : Formula m} (h : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F p q) (move3 (carry h))
  have hOpen' := of_eq (ForcingFreshParentOpening.quantifiedData_rename false (p w) (p z) (p A) (p f) (p B)
    (p b) (p c) (p d) (p t) (p L) (p S) (p Tail) (p Body) (p E) (p ∘ images) u q) (move3 hOpen)
  exact of_eq (SourceAlgebra.rename_comp out p q).symm
    (use e (q ∘ u) x hZ3 carry0 hOpen' hWitness)

-- Open a literal EX with two outer conjuncts at an already selected fresh term.
theorem with_fresh_existential_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B f b c d t L S Tail Body E rM rO N Rest : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hc : Derives Γ (successor c z)) (hd : Derives Γ (successor d b))
    (hCode : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z d t))
    (hBinder : Derives Γ (singleCode 10 w Body Tail))
    (hOuter : Derives Γ (binaryCode 0 w rM Rest Body))
    (hInner : Derives Γ (binaryCode 0 w rO N Rest))
    (hQuery : Derives Γ (substituted w L S A f z b Tail E))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 10 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (r w) (r z) (r A) (r f) (r B) (r b) (r c) (r d) (r t)
        (r L) (r S) (r Tail) (r Body) (r E) v u) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (r w) (u 7) (v 9) (r B) (r f) (r z) (r d)
        (r rM) (r rO) (r N) (r Rest) (u 8) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hInput := SyntaxMixedFormulaOutput.input_of_substituted hZ w L S A f z b Tail E hw hQuery
  have hImages := ForcingWeakenedImages.produce hZ w A f z b d L S (.conjI hw (.conjI hd (.conjR hInput)))
  refine eliminate_objects hZ 10 (fun r v => ForcingWeakenedImages.data
    (r w) (r A) (r f) (r z) (r b) (r d) (r L) (r S) v) hImages out ?_
  intro l Δ r v hZ1 lift hImage
  refine with_fresh_existential_body_at_images hZ1
    (r w) (r z) (r A) (r B) (r f) (r b) (r c) (r d) (r t) (r L) (r S)
    (r Tail) (r Body) (r E) (r rM) (r rO) (r N) (r Rest) v
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename _ _ r) (lift hB)) (of_eq (successor_rename _ _ r) (lift hc))
    (of_eq (successor_rename _ _ r) (lift hd))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ r) (lift hCode))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift ht))
    (of_eq (singleCode_rename _ _ _ _ r) (lift hBinder))
    (of_eq (binaryCode_rename _ _ _ _ _ r) (lift hOuter))
    (of_eq (binaryCode_rename _ _ _ _ _ r) (lift hInner))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hQuery)) hImage (out.rename r) ?_
  intro l' Ξ s u x hZ2 move hOpen hNested
  let e := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm (use e (s ∘ v) u x hZ2 carry hOpen hNested)

/-- Obtain the fresh scope and witness variable from the actual density
existential query, then expose its exact opened body and its three fields. -/
theorem with_fresh_witness_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B f b c L S D E M O rM rO N : Fin m) (nodes : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hc : Derives Γ (successor c z))
    (hs : Derives Γ (ForcingDensityCode.shellData w a A B f M O rM rO N D nodes))
    (hQuery : Derives Γ (substituted w L S A f z b (nodes 2) E))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (d t : Fin l) (v : Fin 10 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (successor d (r b)) →
      Derives Δ (SyntaxVariableSyntax.code false (r w) (r z) t) →
      Derives Δ (SyntaxTermSyntax.term (r w) (r z) d t) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (r w) (r z) (r A) (r f) (r B) (r b) (r c) d t
        (r L) (r S) (r (nodes 2)) (r (nodes 1)) (r E) v u) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (r w) (u 7) (v 9) (r B) (r f) (r z) d
        (r rM) (r rO) (r N) (r (nodes 0)) (u 8) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hType := SyntaxMixedFormulaJudgment.target_type w L S A f z b (nodes 2) E hQuery
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w E z b hType)
  refine eliminate_objects hZ 1 (fun r ds => (Formula.mem (ds 0) (r w)).conj (successor (ds 0) (r b)))
    (.impE (OmegaSyntax.step_at w b (.conjL hw)) (.conjR hCtx)) out ?_
  intro l Δ r ds hZ1 move hD
  let d := ds 0
  have hw1 := of_eq (omega_rename w r) (move hw)
  have hz1 := of_eq (empty_rename z r) (move hz)
  have hZero := SyntaxIndexLiftOrder.zero_member hZ1 (r w) (r b) d (r z) hw1 (move (.conjR hCtx)) (.conjR hD) hz1
  have hTerm := SyntaxTerms.exists_at hZ1 false (r w) (r z) d (r z) hw1
    (.conjI (.conjI (move (.conjL hCtx)) (.conjL hD)) hZero)
  refine eliminate_objects hZ1 1 (fun s ts => (Formula.mem (ts 0) (s (r w))).conj
    ((SyntaxVariableSyntax.code false (s (r w)) (s (r z)) (ts 0)).conj
      (SyntaxTermSyntax.term (s (r w)) (s (r z)) (s d) (ts 0)))) hTerm (out.rename r) ?_
  intro l' Ξ s ts hZ2 move2 hT
  let p := s ∘ r
  let t := ts 0
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename p) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move2 (move h))
  have hD' := of_eq (successor_rename d (r b) s) (move2 (.conjR hD))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  have hS := of_eq (ForcingDensityCode.shellData_rename w a A B f M O rM rO N D nodes p) (carry hs)
  refine with_fresh_existential_body hZ2 (p w) (p z) (p A) (p B) (p f) (p b) (p c) (s d) t
    (p L) (p S) (p (nodes 2)) (p (nodes 1)) (p E) (p rM) (p rO) (p N) (p (nodes 0))
    (of_eq (omega_rename w p) (carry hw)) (of_eq (empty_rename z p) (carry hz))
    (of_eq (successor_rename B A p) (carry hB)) (of_eq (successor_rename c z p) (carry hc))
    hD' (.conjL (.conjR hT)) (.conjR (.conjR hT))
    (.conjL (.conjL (.conjR (.conjR hS)))) (.conjL (.conjL (.conjR hS))) (.conjL (.conjL hS))
    (of_eq (substituted_rename w L S A f z b (nodes 2) E p) (carry hQuery)) (out.rename p) ?_
  intro l'' Ω q v u x hZ3 move3 hOpen hWitness
  let e := q ∘ p
  have carry0 {F : Formula m} (h : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F p q) (move3 (carry h))
  exact of_eq (SourceAlgebra.rename_comp out p q).symm
    (use e (q (s d)) (q t) v u x hZ3 carry0
      (of_eq (successor_rename (s d) (p b) q) (move3 hD'))
      (of_eq (SyntaxVariableSyntax.code_rename false (p w) (p z) t q) (move3 (.conjL (.conjR hT))))
      (of_eq (SyntaxTermSyntax.term_rename (p w) (p z) (s d) t q) (move3 (.conjR (.conjR hT))))
      hOpen hWitness)

/-- At the fresh witness of the actual density existential, read the
rebound body as a direct query of the original forcing code. The bound
table is the actual tail after removing the two inserted conditions. -/
theorem with_direct_witness_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N D b c d t L S X V E Y : Fin m)
    (density : Fin 7 → Fin m) (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m)
    (hA : Derives Γ (successor A a))
    (hDensity : Derives Γ (ForcingDensityCode.data Reln w a A B f j N D density))
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B b c d t L S X V E images opened))
    (hY : Derives Γ (substituted w (opened 7) (images 9) B f z d (density 6) Y))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Q K F : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxTermSyntax.term (r w) (r z) (r d) Q) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r a) (r z) (r d) K) →
      Derives Δ (StructuralListSyntax.consCode (r w) Q K (r (images 8))) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) (r d) (r (images 9)) (r j) (r t) F) →
      Derives Δ (substituted (r w) K F (r a) (r f) (r z) (r d) (r N) (r Y)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hIn := Derives.conjL hOpen
  have hw := Derives.conjL hIn
  have hz := Derives.conjL (.conjR hIn)
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hIn))))))
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists w (images 8) (images 9) A f z d B c (opened 2) (opened 3) hLift
  have hU := Derives.conjL hLists
  have hH := Derives.conjR hLists
  have hUmem := Derives.conjL (.conjL (.conjR (.conjR hU)))
  have htmem := SyntaxTerms.range hZ w z d t hw ht
  have hCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))
  have hRebound := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hDensity)))))
  refine eliminate_objects hZ 1 (fun r ws =>
    (ForcingDensityCode.weakened (r w) (r a) (r A) (r f) (r N) (ws 0)).conj
      (ForcingConditionRebind.compiled (r w) (r A) (r f) (r B) (r j) (ws 0) (r (density 6)))) hRebound out ?_
  intro l Δ r ws hZ1 move hW
  let W := ws 0
  refine eliminate_objects hZ1 3 (fun s xs => ForcingDensityCode.weakenData (s (r w)) (s (r a)) (s (r A)) (s (r f))
    (s (r N)) (s W) xs) (.conjL hW) (out.rename r) ?_
  intro l' Ξ s xs hZ2 move2 hWeak
  let p := s ∘ r
  have carry {G : Formula m} (h : Derives Γ G) : Derives Ξ (G.rename p) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move2 (move h))
  have hw2 := of_eq (omega_rename w p) (carry hw)
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine ForcingExistOrderOpening.with_successor_table hZ2 (p w) (p a) (p A) (p z) (p d) (p (images 8))
    hw2 (of_eq (successor_rename A a p) (carry hA))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w A z d (images 8) p) (carry hU)) (out.rename p) ?_
  intro l'' Ω q Q K hZ3 move3 hQmem hKmem hPrefix hQtype hK
  let u := q ∘ p
  have carry1 {G : Formula m} (h : Derives Γ G) : Derives Ω (G.rename u) :=
    of_eq (SourceAlgebra.rename_comp G p q) (move3 (carry h))
  have hComp := of_eq (ForcingConditionRebind.compiled_rename (r w) (r A) (r f) (r B) (r j) W (r (density 6)) (q ∘ s))
    (of_eq (SourceAlgebra.rename_comp _ s q) (move3 (move2 (.conjR hW))))
  apply of_eq (SourceAlgebra.rename_comp out p q).symm
  refine ForcingExistOrderOpening.with_rebound_prefixed_query hZ3 (u w) (u z) (u A) (u f) (u B) (u z) (u d)
    (u (opened 7)) (u (images 9)) (u (images 8)) (u t) (u j) (q (s W)) (u (density 6)) (u Y)
    (of_eq (omega_rename w u) (carry1 hw)) (of_eq (empty_rename z u) (carry1 hz)) (carry1 htmem) (carry1 hUmem)
    (of_eq (StructuralListSyntax.consCode_rename w t (images 8) (opened 7) u) (carry1 hCons))
    (of_eq (SyntaxTermSyntax.term_rename w z d t u) (carry1 ht))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w A z d (images 8) u) (carry1 hU))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z d (images 9) u) (carry1 hH))
    hComp (of_eq (substituted_rename w (opened 7) (images 9) B f z d (density 6) Y u) (carry1 hY)) (out.rename u) ?_
  intro l''' Θ h F hZ4 move4 hReplacement hRun
  let d' := h ∘ q
  let e := h ∘ u
  have carry0 {G : Formula m} (hp : Derives Γ G) : Derives Θ (G.rename e) :=
    of_eq (SourceAlgebra.rename_comp G u h) (move4 (carry1 hp))
  have hWeak' := of_eq (ForcingDensityCode.weakenData_rename (p w) (p a) (p A) (p f) (p N) (s W) xs d')
    (of_eq (SourceAlgebra.rename_comp _ q h) (move4 (move3 hWeak)))
  have hK' := of_eq (SyntaxMixedImageCodeSyntax.termList_rename (u w) (u a) (u z) (u d) K h) (move4 hK)
  have hPrefix' := of_eq (StructuralListSyntax.consCode_rename (u w) Q K (u (images 8)) h) (move4 hPrefix)
  have hDirect := direct_after_weakening hZ4 (e w) (e a) (e A) (e f) (e z) (e d) (h K) (e (images 8)) F
    (e N) (d' (s W)) (e Y) (d' ∘ xs) (of_eq (omega_rename w e) (carry0 hw)) hK' hWeak' hRun (by
      intro l4 Λ g i I o hZ5 move5 hiw _ hs ho
      exact StructuralListFieldCons.successor_backward hZ5 (g (e w)) (g (h Q)) (g (h K)) (g (e (images 8))) i I o
        (of_eq (omega_rename (e w) g) (move5 (of_eq (omega_rename w e) (carry0 hw))))
        (move5 (move4 hQmem)) (move5 (move4 hKmem)) hiw hs
        (of_eq (StructuralListSyntax.consCode_rename (e w) (h Q) (h K) (e (images 8)) g) (move5 hPrefix')) ho)
  exact of_eq (SourceAlgebra.rename_comp out u h).symm
    (use e (h Q) (h K) F hZ4 carry0
      (of_eq (SyntaxTermSyntax.term_rename (u w) (u z) (u d) Q h) (move4 hQtype)) hK' hPrefix' hReplacement hDirect)

private theorem with_weakened_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A f b d L S Nq Yq : Fin m) (images : Fin 10 → Fin m)
    (hw : Derives Γ (omega w))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S images))
    (hU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w A z d (images 8)))
    (hH : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z d (images 9)))
    (hRun : Derives Γ (substituted w L S A f z b Nq Yq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Y : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r d) (r Yq) Y) →
      Derives Δ (substituted (r w) (r (images 8)) (r (images 9)) (r A) (r f) (r z) (r d) (r Nq) Y) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hTyped := SyntaxMixedFormulaJudgmentTyping.source_type hZ w L S A f z b Nq Yq hw hRun
  have hExists := SyntaxMixedFormulaOutputInduction.actual_exists hZ w (images 8) (images 9) A f z d Nq hw
    (.conjI hTyped (.conjI hU hH))
  refine eliminate_objects hZ 1 (fun r ys => substituted (r w) (r (images 8)) (r (images 9))
    (r A) (r f) (r z) (r d) (r Nq) (ys 0)) hExists out ?_
  intro l Δ r ys hZ1 move hNew
  let Y := ys 0
  have hWeak := ForcingWeakenedImages.from_queries hZ1 (r w) (r A) (r f) (r z) (r b) (r d) (r L) (r S)
    (r Nq) (r Yq) Y (r ∘ images)
    (.conjI (of_eq (ForcingWeakenedImages.data_rename w A f z b d L S images r) (move hImages))
      (.conjI (of_eq (substituted_rename w L S A f z b Nq Yq r) (move hRun)) hNew))
  exact use r Y hZ1 move hWeak hNew

/-- Raise the inherited preorder proof using the actual free image table.
The empty bound column is rebased independently. -/
theorem with_raised_preorder {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A f b d L S R RawPre OldPre H Extra : Fin m) (v : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S v))
    (hOldPre : Derives Γ (substituted w R S z f z b RawPre OldPre))
    (hWeakExtra : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d H Extra))
    (pPre : Derives Γ (implication test w z b H OldPre))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Bnd Pre : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r z) (r z) (r d) Bnd) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r f) (r z) (r d) (r (v 9))) →
      Derives Δ (substituted (r w) Bnd (r (v 9)) (r z) (r f) (r z) (r d) (r RawPre) Pre) →
      Derives Δ (implication test (r w) (r z) (r d) (r Extra) Pre) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hInput := SyntaxMixedFormulaOutput.input_of_substituted hZ w R S z f z b RawPre OldPre hw hOldPre
  have hRebased := ForcingWeakenedImages.rebase_bound hZ w A z f z b d L S R v hImages
    (.conjL (.conjR hInput))
  refine eliminate_objects hZ 3 (fun r x => ForcingWeakenedImages.data
    (r w) (r z) (r f) (r z) (r b) (r d) (r R) (r S)
    (ForcingWeakenedImages.withBound (r ∘ v) (x 0) (x 1) (x 2))) hRebased out ?_
  intro l Δ r x hZ1 lift hRebased1
  let u := ForcingWeakenedImages.withBound (r ∘ v) (x 0) (x 1) (x 2)
  have hLists := SyntaxMixedImageCodePairs.term_lists (r w) (u 6) (u 7) (r z) (r f)
    (r z) (r d) (u 8) (u 9) (.conjR (.conjR (.conjR (.conjR hRebased1))))
  have hw1 := of_eq (omega_rename w r) (lift hw)
  refine with_weakened_query hZ1 (r w) (r z) (r z) (r f) (r b) (r d) (r R) (r S)
    (r RawPre) (r OldPre) u hw1 hRebased1 (.conjL hLists) (.conjR hLists)
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hOldPre)) (out.rename r) ?_
  intro l' Ξ s Pre hZ2 move hWeakPre hPre
  let e := s ∘ r
  have carry {G : Formula m} (h : Derives Γ G) : Derives Ξ (G.rename e) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move (lift h))
  have hw2 := of_eq (omega_rename w e) (carry hw)
  have hz2 := of_eq (empty_rename z e) (carry hz)
  have hs := of_eq (successor_rename d b e) (carry (.conjL (.conjR (.conjL hImages))))
  have hOps := Derives.conjL (.conjR hImages)
  have hi := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z (v 0) e) (carry (.conjL hOps))
  have hj := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b d (v 1) e) (carry (.conjL (.conjR hOps)))
  have hExtra := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (carry hWeakExtra)
  have atPre := ForcingOldParentInstance.raise_implication hZ2 test (e w) (e z) (e b) (e d)
    (e H) (e OldPre) (e Extra) Pre (e (v 0)) (e (v 1)) hw2 hz2 hs hi hj hExtra hWeakPre
    (of_eq (implication_rename test _ _ _ _ _ e) (carry pPre))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use e (s (u 8)) Pre hZ2 carry
      (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ s) (move (.conjL hLists)))
      (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ s) (move (.conjR hLists)))
      hPre atPre)

/-- Reuse the opened witness's maps and free column to raise the inherited
preorder and the old positive proof to the same free scope as the witness.
Only the independent empty bound column of the preorder is rebased. -/
theorem with_raised_witness_proofs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A f b d L S R RawPre OldPre H Extra Yq AtQ : Fin m) (v : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S v))
    (hOldPre : Derives Γ (substituted w R S z f z b RawPre OldPre))
    (hWeakExtra : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d H Extra))
    (hWeakAtQ : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d Yq AtQ))
    (pPre : Derives Γ (implication test w z b H OldPre))
    (pAtQ : Derives Γ (implication test w z b H Yq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Bnd Pre : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r z) (r z) (r d) Bnd) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r f) (r z) (r d) (r (v 9))) →
      Derives Δ (substituted (r w) Bnd (r (v 9)) (r z) (r f) (r z) (r d) (r RawPre) Pre) →
      Derives Δ (implication test (r w) (r z) (r d) (r Extra) Pre) →
      Derives Δ (implication test (r w) (r z) (r d) (r Extra) (r AtQ)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine with_raised_preorder hZ w z A f b d L S R RawPre OldPre H Extra v
    hw hz hImages hOldPre hWeakExtra pPre out ?_
  intro l Δ r Bnd Pre hZ1 lift hBound hFree hPre pPre1
  have hOps := Derives.conjL (.conjR hImages)
  have pAtQ1 := ForcingOldParentInstance.raise_implication hZ1 test (r w) (r z) (r b) (r d)
    (r H) (r Yq) (r Extra) (r AtQ) (r (v 0)) (r (v 1))
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename d b r) (lift (.conjL (.conjR (.conjL hImages)))))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z (v 0) r) (lift (.conjL hOps)))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b d (v 1) r) (lift (.conjL (.conjR hOps))))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeakExtra))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeakAtQ))
    (of_eq (implication_rename test _ _ _ _ _ r) (lift pAtQ))
  exact use r Bnd Pre hZ1 lift hBound hFree hPre pPre1 pAtQ1

private theorem with_weakened_operand {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A f b d L S K Q j C Nq Yq : Fin m) (images : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S images))
    (hU : Derives Γ (SyntaxMixedImageCodeSyntax.termList w A z d (images 8)))
    (hH : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z d (images 9)))
    (hK : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z d K))
    (hQ : Derives Γ (SyntaxTermSyntax.term w z d Q))
    (hPrefix : Derives Γ (StructuralListSyntax.consCode w Q K (images 8)))
    (hComp : Derives Γ (ForcingConditionRebind.compiled w a f A j C Nq))
    (hRun : Derives Γ (substituted w L S A f z b Nq Yq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (F Y : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) (r d) (r (images 9)) (r j) (r Q) F) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r d) (r Yq) Y) →
      Derives Δ (substituted (r w) (r K) F (r a) (r f) (r z) (r d) (r C) Y) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine with_weakened_query hZ w z A f b d L S Nq Yq images hw hImages hU hH hRun out ?_
  intro l Δ r Y hZ1 move hWeak hNew
  refine ForcingExistOrderOpening.with_rebound_prefixed_query hZ1 (r w) (r z) (r a) (r f) (r A) (r z) (r d)
    (r (images 8)) (r (images 9)) (r K) (r Q) (r j) (r C) (r Nq) Y
    (of_eq (omega_rename w r) (move hw)) (of_eq (empty_rename z r) (move hz))
    (move (SyntaxTerms.range hZ w z d Q hw hQ)) (move (.conjL (.conjL (.conjR (.conjR hK)))))
    (of_eq (StructuralListSyntax.consCode_rename w Q K (images 8) r) (move hPrefix))
    (of_eq (SyntaxTermSyntax.term_rename w z d Q r) (move hQ))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w a z d K r) (move hK))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z d (images 9) r) (move hH))
    (of_eq (ForcingConditionRebind.compiled_rename w a f A j C Nq r) (move hComp))
    hNew (out.rename r) ?_
  intro l' Ξ s F hZ2 move2 hReplacement hDirect
  let p := s ∘ r
  have carry {G : Formula m} (hp : Derives Γ G) : Derives Ξ (G.rename p) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move2 (move hp))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use p F (s Y) hZ2 carry hReplacement
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename (r w) (r z) (r b) (r d) (r Yq) Y s) (move2 hWeak)) hDirect)

/-- The weakened operand at the outer condition and the original forcing
code at the witness condition use the very same name table. Both condition
entries come from the two actual prefixes in the opened density record. -/
theorem with_same_name_queries {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N D b c d t L S X V E Y C Nq Yq : Fin m)
    (density : Fin 7 → Fin m) (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m)
    (hA : Derives Γ (successor A a))
    (hDensity : Derives Γ (ForcingDensityCode.data Reln w a A B f j N D density))
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B b c d t L S X V E images opened))
    (hY : Derives Γ (substituted w (opened 7) (images 9) B f z d (density 6) Y))
    (hQComp : Derives Γ (ForcingConditionRebind.compiled w a f A j C Nq))
    (hQRun : Derives Γ (substituted w L S A f z b Nq Yq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Q K Fq Fr Z : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxTermSyntax.term (r w) (r z) (r d) Q) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r a) (r z) (r d) K) →
      Derives Δ (StructuralListSyntax.consCode (r w) Q K (r (images 8))) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) (r d) (r (images 9)) (r j) Q Fq) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) (r d) (r (images 9)) (r j) (r t) Fr) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r d) (r Yq) Z) →
      Derives Δ (substituted (r w) K Fq (r a) (r f) (r z) (r d) (r C) Z) →
      Derives Δ (substituted (r w) K Fr (r a) (r f) (r z) (r d) (r N) (r Y)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hIn := Derives.conjL hOpen
  have hw := Derives.conjL hIn
  have hz := Derives.conjL (.conjR hIn)
  have hImages := Derives.conjL (.conjR hOpen)
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists w (images 8) (images 9) A f z d B c (opened 2) (opened 3) hLift
  refine with_direct_witness_query hZ Reln w z a A B f j N D b c d t L S X V E Y density images opened
    hA hDensity hOpen hY out ?_
  intro l Δ r Q K Fr hZ1 move hQ hK hPrefix hFr hDirectR
  refine with_weakened_operand hZ1 (r w) (r z) (r a) (r A) (r f) (r b) (r d) (r L) (r S) K Q (r j)
    (r C) (r Nq) (r Yq) (r ∘ images) (of_eq (omega_rename w r) (move hw)) (of_eq (empty_rename z r) (move hz))
    (of_eq (ForcingWeakenedImages.data_rename w A f z b d L S images r) (move hImages))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w A z d (images 8) r) (move (.conjL hLists)))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z d (images 9) r) (move (.conjR hLists)))
    hK hQ hPrefix (of_eq (ForcingConditionRebind.compiled_rename w a f A j C Nq r) (move hQComp))
    (of_eq (substituted_rename w L S A f z b Nq Yq r) (move hQRun)) (out.rename r) ?_
  intro l' Ξ s Fq Z hZ2 move2 hFq hWeak hDirectQ
  let p := s ∘ r
  have carry {G : Formula m} (hp : Derives Γ G) : Derives Ξ (G.rename p) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move2 (move hp))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use p (s Q) (s K) Fq (s Fr) Z hZ2 carry
      (of_eq (SyntaxTermSyntax.term_rename (r w) (r z) (r d) Q s) (move2 hQ))
      (of_eq (SyntaxMixedImageCodeSyntax.termList_rename (r w) (r a) (r z) (r d) K s) (move2 hK))
      (of_eq (StructuralListSyntax.consCode_rename (r w) Q K (r (images 8)) s) (move2 hPrefix)) hFq
      (of_eq (ForcingReflexiveImages.replacement_rename (r w) (r f) (r z) (r d) (r (images 9)) (r j) (r t) Fr s) (move2 hFr))
      hWeak hDirectQ
      (of_eq (substituted_rename (r w) K Fr (r a) (r f) (r z) (r d) (r N) (r Y) s) (move2 hDirectR)))



set_option maxHeartbeats 600000 in
/-- Read both actual witness guards in the same scope as the operand
queries. The order guard uses the already selected r table, and its
old head is the q term retained in the actual prefix. The q membership
query is weakened from its actual original output onto that same table. -/
theorem with_witness_guard_results {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Formula (k+2)) (w z a A B f j N D b c d t L S X V E Q K Fr : Fin m)
    (density : Fin 7 → Fin m) (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (guards : Fin 4 → Fin m)
    (I HeadQ SourceQ OldQ H : Fin m)
    (hA : Derives Γ (successor A a))
    (hDensity : Derives Γ (ForcingDensityCode.data R w a A B f j N D density))
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B b c d t L S X V E images opened))
    (hGuards : Derives Γ (ForcingRawModalBody.nestedData 0 w (opened 7) (images 9) B f z d
      (density 4) (density 5) (density 6) I (opened 8) guards))
    (hQ : Derives Γ (SyntaxTermSyntax.term w z d Q))
    (hK : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z d K))
    (hPrefix : Derives Γ (StructuralListSyntax.consCode w Q K (images 8)))
    (hFr : Derives Γ (ForcingReflexiveImages.replacement w f z d (images 9) j t Fr))
    (hHeadQ : Derives Γ (SyntaxVariableSyntax.code true w z HeadQ))
    (hSourceQ : Derives Γ (ForcingGuardCode.compiled false R w A f HeadQ SourceQ))
    (hOldQ : Derives Γ (substituted w L S A f z b SourceQ OldQ))
    (hH : Derives Γ (formulaCode w H z b))
    (pQ : Derives Γ (implication test w z b H OldQ))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (head O Mq Extra Local : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r d) (r H) Extra) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r d) (r OldQ) Mq) →
      Derives Δ (ForcingGuardOpening.result false R (r w) (r z) (r f) (r d) (r Q)
        (r (images 9)) (r A) (r HeadQ) (r SourceQ) Mq) →
      Derives Δ (ForcingGuardOpening.result false R (r w) (r z) (r f) (r d) (r t)
        (r (images 9)) (r B) (r (density 1)) (r (density 4)) (r (guards 1))) →
      Derives Δ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder R) (r w) (r z)
        (r f) (r d) (r Q) (r Fr) (r A) head O (r (guards 2))) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w)
        (SyntaxAtomSyntax.two Extra (r (opened 8))) Local (r z) (r d)) →
      Derives Δ (implication test (r w) (r z) (r d) Local Extra) →
      Derives Δ (implication test (r w) (r z) (r d) Local Mq) →
      Derives Δ (implication test (r w) (r z) (r d) Local (r (guards 1))) →
      Derives Δ (implication test (r w) (r z) (r d) Local (r (guards 2))) →
      Derives Δ (implication test (r w) (r z) (r d) Local (r (guards 3))) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hInput := Derives.conjL hOpen
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hB := Derives.conjL (.conjR (.conjR hInput))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hInput))))))
  have hRCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists w (images 8) (images 9) A f z d B c
    (opened 2) (opened 3) hLift
  have hU := Derives.conjL hLists
  have hFree := Derives.conjR hLists
  have hzA := SyntaxIndexLiftOrder.zero_member hZ w a A z hw (.conjL hK) hA hz
  have hzB := SyntaxIndexLiftOrder.zero_member hZ w A B z hw (.conjL hU) hB hz
  have hTField := StructuralListFieldCons.zero_value hZ w t (images 8) (opened 7) z hw
    (SyntaxTerms.range hZ w z d t hw ht) (.conjL (.conjL (.conjR (.conjR hU)))) hRCons hz
  have hQField := StructuralListFieldCons.zero_value hZ w Q K (images 8) z hw
    (SyntaxTerms.range hZ w z d Q hw hQ) (.conjL (.conjL (.conjR (.conjR hK)))) hPrefix hz
  have hHeadData := Derives.conjL hDensity
  have ez := OmegaUniversal.empty_unique (density 0) z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hHeadData) hz
  have hHead := SyntaxVariableImagePoint.code_subst_index true w (density 0) (density 1) z ez
    (.conjL (.conjR hHeadData))
  have hM := ForcingGuardOpening.from_lifted_at hZ false R w z B f z d (opened 7) (images 9)
    (density 1) t (density 4) (guards 1) hw hz hHead hzB hTField
    (.conjL (.conjR (.conjR (.conjR hDensity)))) (.conjL (.conjR (.conjL hGuards)))
  refine ForcingExistOrderOpening.with_prefixed_guard hZ R w z A B f j d (opened 7) (images 9)
    (images 8) t Q Fr (density 5) (guards 2) hw hz ht hU hRCons hzA hQField hFr
    (.conjL (.conjR (.conjR (.conjR (.conjR hDensity))))) (.conjL (.conjR (.conjR hGuards))) out ?_
  intro l Δ r head O hZ1 lift hOrder
  refine with_weakened_query hZ1 (r w) (r z) (r A) (r f) (r b) (r d) (r L) (r S) (r SourceQ) (r OldQ)
    (r ∘ images) (of_eq (omega_rename w r) (lift hw))
    (of_eq (ForcingWeakenedImages.data_rename w A f z b d L S images r) (lift (.conjL (.conjR hOpen))))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (lift hU))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (lift hFree))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hOldQ)) (out.rename r) ?_
  intro l' Ξ s Mq hZ2 move hWeak hRun
  let ρ := s ∘ r
  have carry {G : Formula m} (h : Derives Γ G) : Derives Ξ (G.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move (lift h))
  have hMemberQ := ForcingGuardOpening.from_lifted_at hZ2 false R (ρ w) (ρ z) (ρ A) (ρ f) (ρ z) (ρ d)
    (ρ (images 8)) (ρ (images 9)) (ρ HeadQ) (ρ Q) (ρ SourceQ) Mq
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (SyntaxVariableSyntax.code_rename true w z HeadQ ρ) (carry hHeadQ)) (carry hzA)
    (of_eq (field_rename _ _ _ _ ρ) (carry hQField))
    (of_eq (ForcingGuardCode.compiled_rename false R _ _ _ _ _ ρ) (carry hSourceQ)) hRun
  have hMaps := of_eq (ForcingWeakenedImages.operations_rename _ _ _ _ _ _ _ _ ρ)
    (carry (.conjL (.conjR (.conjL (.conjR hOpen)))))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hExists := SyntaxWeakenFreeOutput.exists_at_codes hZ2 (ρ w) (ρ z) (ρ b) (ρ d) (ρ H)
    (ρ (images 0)) (ρ (images 1)) hw2
    (of_eq (formulaCode_rename _ _ _ _ ρ) (carry hH)) (.conjL hMaps) (.conjL (.conjR hMaps))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine eliminate_objects hZ2 1 (fun t x => SyntaxWeakenFreeSyntax.weakened
    (t (ρ w)) (t (ρ z)) (t (ρ b)) (t (ρ d)) (t (ρ H)) (x 0)) hExists (out.rename ρ) ?_
  intro l2 Λ τ x hZ3 move2 hExtra
  let e := τ ∘ ρ
  have lift2 {G : Formula m} (h : Derives Γ G) : Derives Λ (G.rename e) :=
    of_eq (SourceAlgebra.rename_comp G ρ τ) (move2 (carry h))
  have hMaps3 := of_eq (ForcingWeakenedImages.operations_rename _ _ _ _ _ _ _ _ τ) (move2 hMaps)
  have hWeakQ := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ τ) (move2 hWeak)
  have pWeakQ := ForcingOldParentInstance.raise_implication hZ3 test (e w) (e z) (e b) (e d)
    (e H) (e OldQ) (x 0) (τ Mq) (e (images 0)) (e (images 1))
    (of_eq (omega_rename w e) (lift2 hw)) (of_eq (empty_rename z e) (lift2 hz))
    (of_eq (successor_rename d b e) (lift2 (.conjL (.conjR (.conjR (.conjR (.conjR hInput)))))))
    (.conjL hMaps3) (.conjL (.conjR hMaps3)) hExtra hWeakQ
    (of_eq (implication_rename test _ _ _ _ _ e) (lift2 pQ))
  have hBodyQuery : Derives Γ (substituted w (opened 7) (images 9) B f z d V (opened 8)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen))))))))
  have query_type (F C : Fin m) (h : Derives Γ (substituted w (opened 7) (images 9) B f z d F C)) :
      Derives Γ (formulaCode w C z d) :=
    SyntaxMixedFormulaJudgment.target_type w (opened 7) (images 9) B f z d F C h
  have hBodyType := query_type V (opened 8) hBodyQuery
  have hOuter := Derives.conjL hGuards
  have hInner := Derives.conjR hGuards
  have hMemberType := query_type (density 4) (guards 1) (.conjL (.conjR hOuter))
  have hInnerType := query_type I (guards 0) (.conjR (.conjR hOuter))
  have hOrderType := query_type (density 5) (guards 2) (.conjL (.conjR hInner))
  have hNegType := query_type (density 6) (guards 3) (.conjR (.conjR hInner))
  have hExtraType := SyntaxWeakenFreeOutput.target_type (e w) (e z) (e b) (e d) (e H) (x 0) hExtra
  have hLocalExists := ForcingProofContext.and_exists hZ3 (e w) (e z) (e d) (x 0) (e (opened 8))
    (of_eq (omega_rename w e) (lift2 hw)) hExtraType (of_eq (formulaCode_rename _ _ _ _ e) (lift2 hBodyType))
  apply of_eq (SourceAlgebra.rename_comp out ρ τ).symm
  refine eliminate_objects hZ3 1 (fun u v => (Formula.mem (v 0) (u (e w))).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (u (e w))
      (SyntaxAtomSyntax.two (u (x 0)) (u (e (opened 8)))) (v 0) (u (e z)) (u (e d))))
    hLocalExists (out.rename e) ?_
  intro l3 Θ κ v hZ4 move3 hLocal
  let ε := κ ∘ e
  have lift3 {G : Formula m} (h : Derives Γ G) : Derives Θ (G.rename ε) :=
    of_eq (SourceAlgebra.rename_comp G e κ) (move3 (lift2 h))
  let Local := v 0
  let Extra := κ (x 0)
  let Body := ε (opened 8)
  let M := ε (guards 1)
  let X := ε (guards 0)
  let Order := ε (guards 2)
  let N := ε (guards 3)
  let Q' := κ (τ Mq)
  have hw4 := of_eq (omega_rename w ε) (lift3 hw)
  have hz4 := of_eq (empty_rename z ε) (lift3 hz)
  have hLT := Derives.conjR (.conjR hLocal)
  have hLC := Derives.conjL (.conjR hLocal)
  have hET := of_eq (formulaCode_rename _ _ _ _ κ) (move3 hExtraType)
  have hBT := of_eq (formulaCode_rename _ _ _ _ ε) (lift3 hBodyType)
  have hMT := of_eq (formulaCode_rename _ _ _ _ ε) (lift3 hMemberType)
  have hXT := of_eq (formulaCode_rename _ _ _ _ ε) (lift3 hInnerType)
  have hOT := of_eq (formulaCode_rename _ _ _ _ ε) (lift3 hOrderType)
  have hNT := of_eq (formulaCode_rename _ _ _ _ ε) (lift3 hNegType)
  have hQT := SyntaxWeakenFreeOutput.target_type (ε w) (ε z) (ε b) (ε d) (ε OldQ) Q'
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ κ) (move3 hWeakQ))
  have pExtra := ForcingRelationGuardProof.project hZ4 test false (ε w) (ε z) (ε d)
    Extra Body Local hw4 hz4 hET hBT hLT hLC
  have pBody := ForcingRelationGuardProof.project hZ4 test true (ε w) (ε z) (ε d)
    Extra Body Local hw4 hz4 hET hBT hLT hLC
  have pMemberQ := ForcingRelationGuardProof.chain hZ4 test (ε w) (ε z) (ε d)
    Local Extra Q' hw4 hz4 hLT hET hQT pExtra
    (of_eq (implication_rename test _ _ _ _ _ κ) (move3 pWeakQ))
  have hBodyCode := of_eq (binaryCode_rename 0 _ _ _ _ ε) (lift3 (.conjL hOuter))
  have hInnerCode := of_eq (binaryCode_rename 0 _ _ _ _ ε) (lift3 (.conjL hInner))
  have pBodyMember := ForcingRelationGuardProof.project hZ4 test false (ε w) (ε z) (ε d)
    M X Body hw4 hz4 hMT hXT hBT hBodyCode
  have pBodyInner := ForcingRelationGuardProof.project hZ4 test true (ε w) (ε z) (ε d)
    M X Body hw4 hz4 hMT hXT hBT hBodyCode
  have pMemberR := ForcingRelationGuardProof.chain hZ4 test (ε w) (ε z) (ε d)
    Local Body M hw4 hz4 hLT hBT hMT pBody pBodyMember
  have pInner := ForcingRelationGuardProof.chain hZ4 test (ε w) (ε z) (ε d)
    Local Body X hw4 hz4 hLT hBT hXT pBody pBodyInner
  have pInnerOrder := ForcingRelationGuardProof.project hZ4 test false (ε w) (ε z) (ε d)
    Order N X hw4 hz4 hOT hNT hXT hInnerCode
  have pInnerNeg := ForcingRelationGuardProof.project hZ4 test true (ε w) (ε z) (ε d)
    Order N X hw4 hz4 hOT hNT hXT hInnerCode
  have pOrder := ForcingRelationGuardProof.chain hZ4 test (ε w) (ε z) (ε d)
    Local X Order hw4 hz4 hLT hXT hOT pInner pInnerOrder
  have pNeg := ForcingRelationGuardProof.chain hZ4 test (ε w) (ε z) (ε d)
    Local X N hw4 hz4 hLT hXT hNT pInner pInnerNeg
  have hOrder4 := of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder R)
    _ _ _ _ _ _ _ _ _ _ (κ ∘ τ ∘ s))
    (of_eq (by simp only [SourceAlgebra.rename_comp]; rfl) (move3 (move2 (move hOrder))))
  have hMemberQ4 := of_eq (ForcingGuardOpening.result_rename false R _ _ _ _ _ _ _ _ _ _ (κ ∘ τ))
    (of_eq (SourceAlgebra.rename_comp _ τ κ) (move3 (move2 hMemberQ)))
  exact of_eq (SourceAlgebra.rename_comp out e κ).symm
    (use ε (κ (τ (s head))) (κ (τ (s O))) Q' Extra Local hZ4 lift3
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ κ) (move3 hExtra))
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ κ) (move3 hWeakQ)) hMemberQ4
      (of_eq (ForcingGuardOpening.result_rename false R _ _ _ _ _ _ _ _ _ _ ε) (lift3 hM))
      hOrder4 (.conjR hLocal) pExtra pMemberQ pMemberR pOrder pNeg)

set_option maxHeartbeats 800000 in
/-- Open the actual density existential from the original negative branch.
The old positive operand and the membership at q are read from the original
negative tail, transported to the identical outer table and weakened to the
witness scope. -/
theorem with_negative_witness_queries {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f j N C b c d t L S D E G W H body Parent Yq Bot : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (negData : Fin 5 → Fin m)
    (negNodes negOut : Fin 4 → Fin m)
    (hB : Derives Γ (successor B A))
    (hNeg : Derives Γ (ForcingRawModalBody.negativeRecord Reln w z a f A b c d t L S j C N body Parent
      images negOpen negData negNodes))
    (hNegQueries : Derives Γ (ForcingRawModalBody.data w (negOpen 7) (images 9) A f z d
      (negData 3) (negData 4) (negNodes 1) (negNodes 2) (negOpen 8) negOut))
    (hOperand : Derives Γ (ForcingFormulaDiagram.binaryData 2 w (negOpen 7) (images 9) A f z d
      (negData 2) (negNodes 0) (negOut 3) Yq Bot))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (hM : Derives Γ (implication test w z d H (negOut 1)))
    (hO : Derives Γ (implication test w z d H (negOut 2)))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (B' T Q K Fq Fr Z Zr Tail Bound OrderHead OrderSource MemberQ Extra Local : Fin l)
      (density : Fin 7 → Fin l) (shell : Fin 5 → Fin l) (v : Fin 10 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (implication test (r w) (r z) (r d) (r H) Tail) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (r w) (r z) (r A) (r f) (r B)
        (r d) (r c) B' T Bound (r (images 9)) (shell 2) (shell 1) Tail v u) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (r w) (u 7) (v 9) (r B) (r f) (r z) B'
        (density 4) (density 5) (density 6) (shell 0) (u 8) x) →
      Derives Δ (SyntaxTermSyntax.term (r w) (r z) B' Q) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (r w) (r a) (r z) B' K) →
      Derives Δ (SyntaxRenameTermSyntax.renamed (r w) (v 2) (v 3) (r z) (r d) (r z) B' (r t) Q) →
      Derives Δ (StructuralListSyntax.consCode (r w) Q K (v 8)) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) B' (v 9) (r j) Q Fq) →
      Derives Δ (ForcingReflexiveImages.replacement (r w) (r f) (r z) B' (v 9) (r j) T Fr) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r d) B' (r Yq) Z) →
      Derives Δ (substituted (r w) K Fq (r a) (r f) (r z) B' (r C) Z) →
      Derives Δ (substituted (r w) K Fr (r a) (r f) (r z) B' (r C) Zr) →
      Derives Δ (substituted (r w) K Fr (r a) (r f) (r z) B' (r N) (x 3)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r d) B' (r H) Extra) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r d) B' (r (negOut 1)) MemberQ) →
      Derives Δ (ForcingGuardOpening.result false Reln (r w) (r z) (r f) B' Q
        (v 9) (r A) (r (negData 1)) (r (negData 3)) MemberQ) →
      Derives Δ (ForcingGuardOpening.result false Reln (r w) (r z) (r f) B' T
        (v 9) (r B) (density 1) (density 4) (x 1)) →
      Derives Δ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln) (r w) (r z)
        (r f) B' Q Fr (r A) OrderHead OrderSource (x 2)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w)
        (SyntaxAtomSyntax.two Extra (u 8)) Local (r z) B') →
      Derives Δ (implication test (r w) (r z) B' Local Extra) →
      Derives Δ (implication test (r w) (r z) B' Local MemberQ) →
      Derives Δ (implication test (r w) (r z) B' Local (x 1)) →
      Derives Δ (implication test (r w) (r z) B' Local (x 2)) →
      Derives Δ (implication test (r w) (r z) B' Local (x 3)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hParent := Derives.conjL hNeg
  have hInput := Derives.conjL hParent
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hA := Derives.conjL (.conjR (.conjR hInput))
  have hc := Derives.conjL (.conjR (.conjR (.conjR hInput)))
  have hT := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hInput))))))
  have hOldCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hParent)))))))
  have hOldLift := Derives.conjL (.conjR (.conjR (.conjR hParent)))
  have hOldLists := SyntaxCodedMixedBinderTyping.input_lists w (images 8) (images 9) a f z d A c
    (negOpen 2) (negOpen 3) hOldLift
  have hOldHead := StructuralListFieldCons.zero_value hZ w t (images 8) (negOpen 7) z hw
    (SyntaxTerms.range hZ w z d t hw hT) (.conjL (.conjL (.conjR (.conjR (.conjL hOldLists))))) hOldCons hz
  have hRebind : Derives Γ (ForcingConditionRebind.compiled w a f A j C (negData 2)) :=
    .conjL (.conjR (.conjL (.conjR hNeg)))
  have hOld := Derives.conjL (.conjR hOperand)
  have hOldMember := Derives.conjL (.conjR (.conjL hNegQueries))
  have hNegCompiler := Derives.conjL (.conjR hNeg)
  have hHeadData := Derives.conjL hNegCompiler
  have eEmpty := OmegaUniversal.empty_unique (negData 0) z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hHeadData) hz
  have hHeadQ := SyntaxVariableImagePoint.code_subst_index true w (negData 0) (negData 1) z eEmpty
    (.conjL (.conjR hHeadData))
  have hMemberSource := Derives.conjL (.conjR (.conjR hNegCompiler))
  refine with_negative_density_tail hZ Reln w z a A B f j N C b c d t L S D E G W H body Parent
    images negOpen negData negNodes negOut hNeg hNegQueries hCompiled hQuery hWeakG hProof
    hH hW hToW hM hO out ?_
  intro l Δ r v s u x hZ1 move eList hDensity hShell _ hRuns hTail
  have hQ := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (negOpen 7)) (r (images 9))
    (r A) (r f) (r z) (r d) (r (negData 2)) (r Yq) (u 7) eList
    (of_eq (substituted_rename w (negOpen 7) (images 9) A f z d (negData 2) Yq r) (move hOld))
  have hMemberOnTable := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (negOpen 7)) (r (images 9))
    (r A) (r f) (r z) (r d) (r (negData 3)) (r (negOut 1)) (u 7) eList
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (move hOldMember))
  let Head := StructuralListFieldSyntax.field (r w).castSucc (Fin.last l) (r z).castSucc (r t).castSucc
  have headAt (i : Fin l) : Head.instantiate i = StructuralListFieldSyntax.field (r w) i (r z) (r t) := by
    simp only [Head, Formula.instantiate, StructuralListFieldSyntax.field_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hHead := of_eq (headAt (u 7)) (.eqSubst Head eList (of_eq (headAt (r (negOpen 7))).symm
    (of_eq (StructuralListFieldSyntax.field_rename w (negOpen 7) z t r) (move hOldHead))))
  have hEx := Derives.conjR (.conjR (.conjR hRuns))
  refine with_fresh_witness_records hZ1 (r w) (r z) (r a) (r A) (r B) (r f) (r d) (r c)
    (u 7) (r (images 9)) (r D) (x 3) (v 2) (v 3) (v 4) (v 5) (v 6) s
    (of_eq (omega_rename w r) (move hw)) (of_eq (empty_rename z r) (move hz))
    (of_eq (successor_rename B A r) (move hB)) (of_eq (successor_rename c z r) (move hc))
    hShell hEx (out.rename r) ?_
  intro l' Ξ p d' t' v' u' x' hZ2 move2 _ _ _ hOpen hWitness
  let ρ := p ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F r p) (move2 (move h))
  apply of_eq (SourceAlgebra.rename_comp out r p).symm
  refine with_same_name_queries hZ2 Reln (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j)
    (ρ N) (ρ D) (ρ d) (ρ c) d' t' (p (u 7)) (ρ (images 9)) (p (s 2)) (p (s 1))
    (p (x 3)) (x' 3) (ρ C) (ρ (negData 2)) (ρ Yq) (p ∘ v) v' u'
    (of_eq (successor_rename A a ρ) (carry hA))
    (of_eq (ForcingDensityCode.data_rename Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v p) (move2 hDensity))
    hOpen (.conjR (.conjR (.conjR hWitness)))
    (of_eq (ForcingConditionRebind.compiled_rename w a f A j C (negData 2) ρ) (carry hRebind))
    (of_eq (substituted_rename (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) (r (negData 2)) (r Yq) p) (move2 hQ))
    (out.rename ρ) ?_
  intro l'' Ω q Q K Fq Fr Z hZ3 move3 hQType hK hPrefix hFq hFr hWeak hPositive hNegative
  let e := q ∘ ρ
  have lift {F : Formula m} (h : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F ρ q) (move3 (carry h))
  have hw3 := of_eq (omega_rename w e) (lift hw)
  have hz3 := of_eq (empty_rename z e) (lift hz)
  have hzA := SyntaxIndexLiftOrder.zero_member hZ3 (e w) (e a) (e A) (e z) hw3 (.conjL hK)
    (of_eq (successor_rename A a e) (lift hA)) hz3
  have hOldHead3 := of_eq (StructuralListFieldSyntax.field_rename (r w) (u 7) (r z) (r t) (q ∘ p))
    (of_eq (SourceAlgebra.rename_comp _ p q) (move3 (move2 hHead)))
  have hNewHead := StructuralListFieldCons.zero_value hZ3 (e w) Q K (q (v' 8)) (e z) hw3
    (SyntaxTerms.range hZ3 (e w) (e z) (q d') Q hw3 hQType)
    (.conjL (.conjL (.conjR (.conjR hK)))) hPrefix hz3
  have hOpen3 := of_eq (ForcingFreshParentOpening.quantifiedData_rename false (ρ w) (ρ z) (ρ A) (ρ f) (ρ B)
    (ρ d) (ρ c) d' t' (p (u 7)) (ρ (images 9)) (p (s 2)) (p (s 1)) (p (x 3)) v' u' q) (move3 hOpen)
  have hRename := Derives.impE (.conjL (ForcingReindexedImages.field_iff hZ3 true
    (e w) (e A) (e f) (e z) (e d) (e z) (q d') (q (p (u 7))) (e (images 9))
    (q (v' 2)) (q (v' 3)) (e z) (e t) Q (fun i => q (v' (i.addNat 4)))
    (.conjR (.conjR (.conjL (.conjR hOpen3)))) (.conjI hzA hOldHead3))) (.conjI hzA hNewHead)
  have hTail3 := of_eq (implication_rename test (ρ w) (ρ z) (ρ d) (ρ H) (p (x 3)) q)
    (move3 (of_eq (implication_rename test (r w) (r z) (r d) (r H) (x 3) p) (move2 hTail)))
  have hWitness3 := of_eq (ForcingRawModalBody.nestedData_rename 0 (ρ w) (u' 7) (v' 9) (ρ B) (ρ f) (ρ z) d'
    (p (v 4)) (p (v 5)) (p (v 6)) (p (s 0)) (u' 8) x' q) (move3 hWitness)
  have hC := SyntaxMixedFormulaJudgmentTyping.source_type hZ3 (e w) K Fq (e a) (e f) (e z) (q d') (e C) Z hw3 hPositive
  have hFrList := ForcingReflexiveImages.target_type (e w) (e f) (e z) (q d') (q (v' 9)) (e j) (q t') Fr hFr
  have hCr := SyntaxMixedFormulaOutputInduction.actual_exists hZ3 (e w) K Fr (e a) (e f) (e z) (q d') (e C)
    hw3 (.conjI hC (.conjI hK hFrList))
  apply of_eq (SourceAlgebra.rename_comp out ρ q).symm
  refine eliminate_objects hZ3 1 (fun s ys => substituted (s (e w)) (s K) (s Fr) (s (e a)) (s (e f))
    (s (e z)) (s (q d')) (s (e C)) (ys 0)) hCr (out.rename e) ?_
  intro l3 Λ g ys hZ4 move4 hAtR
  let R := g ∘ e
  have finalLift {F : Formula m} (h : Derives Γ F) : Derives Λ (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F e g) (move4 (lift h))
  let U := g ∘ q ∘ p
  have hDensity4 := of_eq (ForcingDensityCode.data_rename Reln (r w) (r a) (r A) (r B) (r f)
    (r j) (r N) (r D) v U)
    (of_eq (SourceAlgebra.rename_comp _ p (g ∘ q))
      (of_eq (SourceAlgebra.rename_comp _ q g) (move4 (move3 (move2 hDensity)))))
  have hOpen4 := of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (move4 hOpen3)
  have hWitness4 := of_eq (ForcingRawModalBody.nestedData_rename 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _) (move4 hWitness3)
  have hMemberOnTable4 := of_eq (substituted_rename (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
    (r (negData 3)) (r (negOut 1)) U)
    (of_eq (SourceAlgebra.rename_comp _ p (g ∘ q))
      (of_eq (SourceAlgebra.rename_comp _ q g) (move4 (move3 (move2 hMemberOnTable)))))
  apply of_eq (SourceAlgebra.rename_comp out e g).symm
  refine with_witness_guard_results hZ4 Reln (R w) (R z) (R a) (R A) (R B) (R f) (R j) (R N) (R D) (R d)
    (R c) (g (q d')) (g (q t')) (g (q (p (u 7)))) (R (images 9)) (U (s 2)) (U (s 1)) (U (x 3))
    (g Q) (g K) (g Fr) (U ∘ v) (g ∘ q ∘ v') (g ∘ q ∘ u') (g ∘ q ∘ x') (U (s 0))
    (R (negData 1)) (R (negData 3)) (R (negOut 1)) (R H)
    (of_eq (successor_rename A a R) (finalLift hA)) hDensity4 hOpen4 hWitness4
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (move4 hQType))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (move4 hK))
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ _) (move4 hPrefix))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ _) (move4 hFr))
    (of_eq (SyntaxVariableSyntax.code_rename true _ _ _ _) (finalLift hHeadQ))
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ _) (finalLift hMemberSource))
    hMemberOnTable4 (of_eq (formulaCode_rename _ _ _ _ R) (finalLift hH))
    (of_eq (implication_rename test _ _ _ _ _ R) (finalLift hM)) (out.rename R) ?_
  intro l4 Ψ i OrderHead OrderSource MemberQ Extra Local hZ5 move5 hWeakExtra hWeakMember hMemberQ hMember hOrder
    hLocal pExtra pMemberQ pMemberR pOrder pNeg
  let σ := i ∘ g
  let ψ := i ∘ R
  have last {F : Formula l''} (h : Derives Ω F) : Derives Ψ (F.rename σ) :=
    of_eq (SourceAlgebra.rename_comp F g i) (move5 (move4 h))
  have original {F : Formula m} (h : Derives Γ F) : Derives Ψ (F.rename ψ) :=
    of_eq (SourceAlgebra.rename_comp F R i) (move5 (finalLift h))
  exact of_eq (SourceAlgebra.rename_comp out R i).symm
    (use ψ (σ (q d')) (σ (q t')) (σ Q) (σ K) (σ Fq) (σ Fr) (σ Z) (i (ys 0))
      (σ (q (p (x 3)))) (σ (q (p (u 7)))) OrderHead OrderSource MemberQ Extra Local
      (i ∘ U ∘ v) (i ∘ U ∘ s) (σ ∘ q ∘ v') (σ ∘ q ∘ u') (σ ∘ q ∘ x') hZ5 original
      (of_eq (implication_rename test _ _ _ _ _ σ) (last hTail3))
      (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ) (last hOpen3))
      (of_eq (ForcingRawModalBody.nestedData_rename 0 _ _ _ _ _ _ _ _ _ _ _ _ _ σ) (last hWitness3))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ σ) (last hQType))
      (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ σ) (last hK))
      (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ σ) (last hRename))
      (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ σ) (last hPrefix))
      (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ σ) (last hFq))
      (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ σ) (last hFr))
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ σ) (last hWeak))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ σ) (last hPositive))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ i) (move5 hAtR))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ σ) (last hNegative)) hWeakExtra hWeakMember hMemberQ hMember hOrder
      hLocal pExtra pMemberQ pMemberR pOrder pNeg)


/-- The literal target existential tail at q after the first witness has
been opened. The query and its weakening use the same compiler output. -/
def weakenedTailResult {m} (w z A f b B L S Tail Y : Fin m) : Formula m :=
  existsMany 1 ((SyntaxWeakenFreeSyntax.weakened (old 1 w) (old 1 z) (old 1 b) (old 1 B)
    (old 1 Y) (slot 1 0)).conj
      (substituted (old 1 w) (old 1 L) (old 1 S) (old 1 A) (old 1 f) (old 1 z)
        (old 1 B) (old 1 Tail) (slot 1 0)))

theorem weakenedTailResult_rename {m l} (w z A f b B L S Tail Y : Fin m) (r : Fin m → Fin l) :
    (weakenedTailResult w z A f b B L S Tail Y).rename r =
      weakenedTailResult (r w) (r z) (r A) (r f) (r b) (r B) (r L) (r S) (r Tail) (r Y) := by
  simp only [weakenedTailResult, existsMany_rename, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
    substituted_rename, lift_old, lift_slot]

/-- At q in the original existential density clause, open the actual
density witness r. The final body query is the original existential
compiler at r on its selected condition table. -/
theorem with_existential_density_witness {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j N Child b c d t L S D E G W H body Parent : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (compiler : Fin 8 → Fin m)
    (nodes : Fin 7 → Fin m) (outputs : Fin 4 → Fin m)
    (hB : Derives Γ (successor B A))
    (hExist : Derives Γ (ForcingRawModalBody.existentialRecord Reln Dom w z a f A B C b c d t L S
      j Child N body Parent images opened compiler nodes))
    (hQueries : Derives Γ (ForcingRawModalBody.data w (opened 7) (images 9) A f z d
      (compiler 2) (compiler 3) (nodes 4) (nodes 5) (opened 8) outputs))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (pQ : Derives Γ (implication test w z d H (outputs 1)))
    (pOrder : Derives Γ (implication test w z d H (outputs 2)))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l)
      (B' T Q K Fr Tail Bound OrderHead OrderCode MemberQ Extra Local : Fin l)
      (density : Fin 7 → Fin l) (shell : Fin 5 → Fin l) (v : Fin 10 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename ρ)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ d) (ρ H) Tail) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (ρ w) (ρ z) (ρ A) (ρ f) (ρ B)
        (ρ d) (ρ c) B' T Bound (ρ (images 9)) (shell 2) (shell 1) Tail v u) →
      Derives Δ (SyntaxTermSyntax.term (ρ w) (ρ z) B' Q) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termList (ρ w) (ρ a) (ρ z) B' K) →
      Derives Δ (StructuralListSyntax.consCode (ρ w) Q K (v 8)) →
      Derives Δ (weakenedTailResult (ρ w) (ρ z) (ρ A) (ρ f) (ρ d) B' (v 8) (v 9)
        (ρ (nodes 4)) (ρ (outputs 3))) →
      Derives Δ (ForcingReflexiveImages.replacement (ρ w) (ρ f) (ρ z) B' (v 9) (ρ j) T Fr) →
      Derives Δ (substituted (ρ w) K Fr (ρ a) (ρ f) (ρ z) B' (ρ N) (x 3)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (ρ w) (ρ z) (ρ d) B' (ρ H) Extra) →
      Derives Δ (ForcingGuardOpening.result false Reln (ρ w) (ρ z) (ρ f) B' Q
        (v 9) (ρ A) (ρ (compiler 1)) (ρ (compiler 2)) MemberQ) →
      Derives Δ (ForcingGuardOpening.result false Reln (ρ w) (ρ z) (ρ f) B' T
        (v 9) (ρ B) (density 1) (density 4) (x 1)) →
      Derives Δ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln) (ρ w) (ρ z)
        (ρ f) B' Q Fr (ρ A) OrderHead OrderCode (x 2)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (ρ w)
        (SyntaxAtomSyntax.two Extra (u 8)) Local (ρ z) B') →
      Derives Δ (implication test (ρ w) (ρ z) B' Local Extra) →
      Derives Δ (implication test (ρ w) (ρ z) B' Local MemberQ) →
      Derives Δ (implication test (ρ w) (ρ z) B' Local (x 1)) →
      Derives Δ (implication test (ρ w) (ρ z) B' Local (x 2)) →
      Derives Δ (implication test (ρ w) (ρ z) B' Local (x 3)) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  have hParent := Derives.conjL hExist
  have hInput := Derives.conjL hParent
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hA := Derives.conjL (.conjR (.conjR hInput))
  have hc := Derives.conjL (.conjR (.conjR (.conjR hInput)))
  have hCompiler := Derives.conjL (.conjR hExist)
  have hHead := Derives.conjL hCompiler
  have hMember := Derives.conjL (.conjR hCompiler)
  have hOrder := Derives.conjL (.conjR (.conjR hCompiler))
  have eZero := OmegaUniversal.empty_unique (compiler 0) z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hHead) hz
  have hVar := SyntaxVariableImagePoint.code_subst_index true w (compiler 0) (compiler 1) z eZero
    (.conjL (.conjR hHead))
  have hAtQ := Derives.conjL (.conjR (.conjL hQueries))
  refine with_opened_density_tail hZ Reln w z a A B f j N b c d t L S D E G W H body Parent
    (compiler 0) (compiler 1) (compiler 2) (compiler 3) (nodes 4) (nodes 5)
    images opened outputs hParent (.conjL hHead) (.conjL (.conjR hHead)) hMember hOrder
    hQueries hCompiled hQuery hWeakG hProof hH hW hToW pQ pOrder out ?_
  intro l Δ r v s u x hZ1 lift eList hDensity hShell _ hRuns pTail
  have hAtQ1 := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (opened 7)) (r (images 9))
    (r A) (r f) (r z) (r d) (r (compiler 2)) (r (outputs 1)) (u 7) eList
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hAtQ))
  have hAtQTail := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (opened 7)) (r (images 9))
    (r A) (r f) (r z) (r d) (r (nodes 4)) (r (outputs 3)) (u 7) eList
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift (.conjR (.conjR (.conjR hQueries)))))
  refine with_fresh_witness_records hZ1 (r w) (r z) (r a) (r A) (r B) (r f) (r d) (r c)
    (u 7) (r (images 9)) (r D) (x 3) (v 2) (v 3) (v 4) (v 5) (v 6) s
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename _ _ r) (lift hB)) (of_eq (successor_rename _ _ r) (lift hc))
    hShell (.conjR (.conjR (.conjR hRuns))) (out.rename r) ?_
  intro l1 Δ1 σ B' T v' u' x' hZ2 move _ _ _ hOpening hWitness
  let e := σ ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r σ) (move (lift h))
  have hDensity1 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ v σ) (move hDensity)
  apply of_eq (SourceAlgebra.rename_comp out r σ).symm
  refine with_direct_witness_query hZ2 Reln (e w) (e z) (e a) (e A) (e B) (e f) (e j) (e N) (e D)
    (e d) (e c) B' T (σ (u 7)) (e (images 9)) (σ (s 2)) (σ (s 1)) (σ (x 3)) (x' 3)
    (σ ∘ v) v' u' (of_eq (successor_rename _ _ e) (carry hA)) hDensity1 hOpening
    (.conjR (.conjR (.conjR hWitness))) (out.rename e) ?_
  intro l2 Δ2 τ Q K Fr hZ3 move2 hQ hK hPrefix hFr hDirect
  let η := τ ∘ e
  have carry2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename η) :=
    of_eq (SourceAlgebra.rename_comp F e τ) (move2 (carry h))
  have cross {F : Formula l} (h : Derives Δ F) : Derives Δ2 (F.rename (τ ∘ σ)) :=
    of_eq (SourceAlgebra.rename_comp F σ τ) (move2 (move h))
  have hOpening2 := of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _
    v' u' τ) (move2 hOpening)
  have hWitness2 := of_eq (ForcingRawModalBody.nestedData_rename 0 _ _ _ _ _ _ _ _ _ _ _ _ x' τ)
    (move2 hWitness)
  have hImages := Derives.conjL (.conjR hOpening2)
  have hLists := SyntaxMixedImageCodePairs.term_lists (η w) (τ (v' 6)) (τ (v' 7)) (η A) (η f)
    (η z) (τ B') (τ (v' 8)) (τ (v' 9)) (.conjR (.conjR (.conjR (.conjR hImages))))
  let target := weakenedTailResult (η w) (η z) (η A) (η f) (η d) (τ B')
    (τ (v' 8)) (τ (v' 9)) (η (nodes 4)) (η (outputs 3))
  have hTarget : Derives Δ2 target := by
    refine with_weakened_query hZ3 (η w) (η z) (η A) (η f) (η d) (τ B')
      (τ (σ (u 7))) (η (images 9)) (η (nodes 4)) (η (outputs 3)) (τ ∘ v')
      (of_eq (omega_rename _ η) (carry2 hw)) hImages (.conjL hLists) (.conjR hLists)
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (τ ∘ σ)) (cross hAtQTail)) target ?_
    intro l' Ξ r Y hZ' lift' hWeak hQuery
    apply of_eq (weakenedTailResult_rename _ _ _ _ _ _ _ _ _ _ r).symm
    apply HornBinderRules.intro_many 1 _ (fun _ => Y)
    exact of_eq (by simp only [Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
      substituted_rename, assign_old, assign_slot]; rfl) (.conjI hWeak hQuery)
  apply of_eq (SourceAlgebra.rename_comp out e τ).symm
  refine with_witness_guard_results hZ3 Reln (η w) (η z) (η a) (η A) (η B) (η f) (η j) (η N) (η D)
    (η d) (η c) (τ B') (τ T) (τ (σ (u 7))) (η (images 9)) (τ (σ (s 2))) (τ (σ (s 1))) (τ (σ (x 3)))
    Q K Fr (τ ∘ σ ∘ v) (τ ∘ v') (τ ∘ u') (τ ∘ x')
    (τ (σ (s 0))) (η (compiler 1)) (η (compiler 2)) (η (outputs 1)) (η H)
    (of_eq (successor_rename _ _ η) (carry2 hA))
    (of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ (σ ∘ v) τ) (move2 hDensity1))
    hOpening2 hWitness2 hQ hK hPrefix hFr
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ η) (carry2 hVar))
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ η) (carry2 hMember))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (τ ∘ σ)) (cross hAtQ1))
    (of_eq (formulaCode_rename _ _ _ _ η) (carry2 hH))
    (of_eq (implication_rename test _ _ _ _ _ η) (carry2 pQ)) (out.rename η) ?_
  intro l3 Δ3 κ head order Mq Extra Local hZ4 move3 hWeak _ hMQ hMR hO hLocal pExtra pMQ pMR pO pAtR
  let ρ := κ ∘ η
  have carry3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F η κ) (move3 (carry2 h))
  have cross2 {F : Formula l} (h : Derives Δ F) : Derives Δ3 (F.rename (κ ∘ τ ∘ σ)) :=
    of_eq (SourceAlgebra.rename_comp F (τ ∘ σ) κ) (move3 (cross h))
  exact of_eq (SourceAlgebra.rename_comp out η κ).symm
    (use ρ (κ (τ B')) (κ (τ T)) (κ Q) (κ K) (κ Fr) (κ (τ (σ (x 3)))) (κ (τ (σ (u 7))))
      head order Mq Extra Local (κ ∘ τ ∘ σ ∘ v) (κ ∘ τ ∘ σ ∘ s) (κ ∘ τ ∘ v') (κ ∘ τ ∘ u')
      (κ ∘ τ ∘ x') hZ4 carry3
      (of_eq (implication_rename test _ _ _ _ _ (κ ∘ τ ∘ σ)) (cross2 pTail))
      (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (τ ∘ v') (τ ∘ u') κ) (move3 hOpening2))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ κ) (move3 hQ))
      (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ κ) (move3 hK))
      (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ κ) (move3 hPrefix))
      (of_eq (weakenedTailResult_rename _ _ _ _ _ _ _ _ _ _ κ) (move3 hTarget))
      (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ κ) (move3 hFr))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ κ) (move3 hDirect))
      hWeak hMQ hMR hO hLocal pExtra pMQ pMR pO pAtR)


end PPAC.Migration.ForcingDensityInstantiation
