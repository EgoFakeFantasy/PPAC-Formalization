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
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 5 (fun t o => openedData (t (R w)) (t (R z)) (t (R a)) (t (R f)) (t (R b))
    (t (R L)) (t (R S)) (t (R E)) (t (R p)) (t (R G)) (t (ds 2)) (t (ds 3))
    (t (u 2)) (t (u 3)) (t (u 4)) o) (.conjR hs) (out.rename R) ?_
  intro l2 Δ2 t o hZ3 lift2 ho
  let Q := t ∘ R
  let dt := t ∘ ds
  let ut := t ∘ u
  have move2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename Q) :=
    of_eq (SourceAlgebra.rename_comp F R t) (lift2 (move h))
  have hData2 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ ds t) (lift2 hData)
  have hShell := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ u t) (lift2 (.conjL hs))
  have hLift := Derives.conjL (.conjR ho)
  refine of_eq (SourceAlgebra.rename_comp out R t).symm ?_
  refine eliminate_objects hZ3 4 (fun e y => pointGuardsData (e (Q w)) (e (Q z)) (e (o 1)) (e (Q f)) (e (o 2))
    (e (Q b)) (e (o 3)) (e (o 4)) (e (o 0)) (e (Q p)) (e (Q G)) (e (dt 2)) (e (dt 3)) (e (ut 2)) (e (ut 3)) y)
    (.conjR (.conjR (.conjR ho))) (out.rename Q) ?_
  intro l3 Δ3 e y hZ4 lift3 hy
  let T := e ∘ Q
  let de := e ∘ dt
  let ue := e ∘ ut
  let oe := e ∘ o
  have move3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename T) :=
    of_eq (SourceAlgebra.rename_comp F Q e) (lift3 (move2 h))
  have hData3 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ dt e) (lift3 hData2)
  have hShell3 := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ ut e) (lift3 hShell)
  have hLift3 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ e) (lift3 hLift)
  refine of_eq (SourceAlgebra.rename_comp out Q e).symm ?_
  refine eliminate_objects hZ4 4 (fun h v => pointData (h (T w)) (h (T z)) (h (T b)) (h (oe 0))
    (h (T p)) (h (T G)) (h (y 1)) (h (y 2)) (h (y 3)) (h (y 0)) v)
    (.conjR hy) (out.rename T) ?_
  intro l4 Δ4 h v hZ5 lift4 hv
  let P := h ∘ T
  let dh := h ∘ de
  let uh := h ∘ ue
  let oh := h ∘ oe
  let yh := h ∘ y
  have move4 {F : Formula m} (hp : Derives Γ F) : Derives Δ4 (F.rename P) :=
    of_eq (SourceAlgebra.rename_comp F T h) (lift4 (move3 hp))
  have hData4 := of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ de h) (lift4 hData3)
  have hShell4 := of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ ue h) (lift4 hShell3)
  have hLift4 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ h) (lift4 hLift3)
  have hRaw4 := of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ y h) (lift4 (.conjL hy))
  refine of_eq (SourceAlgebra.rename_comp out T h).symm ?_
  refine eliminate_objects hZ5 4 (fun i x => ForcingRawModalBody.data (i (P w)) (i (v 2)) (i (v 3))
    (i (v 0)) (i (P b)) (i (P z)) (i (P b)) (i (yh 1)) (i (yh 2)) (i (yh 3)) (i (yh 0)) (i (v 1)) x)
    (.conjL (.conjR (.conjR hv))) (out.rename P) ?_
  intro l5 Δ5 i x hZ6 lift5 hx
  let F := i ∘ P
  have move5 {U : Formula m} (hp : Derives Γ U) : Derives Δ5 (U.rename F) :=
    of_eq (SourceAlgebra.rename_comp U P i) (lift5 (move4 hp))
  exact of_eq (SourceAlgebra.rename_comp out P i).symm
    (use F (i ∘ dh) (i ∘ uh) (i ∘ oh) (i ∘ yh) (i ∘ v) x hZ6 move5
      (of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ dh i) (lift5 hData4))
      (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ uh i) (lift5 hShell4))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ i) (lift5 hLift4))
      (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ yh i) (lift5 hRaw4))
      (of_eq (pointData_rename _ _ _ _ _ _ _ _ _ _ v i) (lift5 hv)) hx)

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
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) v) →
      Derives Δ (ForcingDensityCode.shellData (r w) (r a) (r A) (r B) (r f) (v 2) (v 3) (v 4) (v 5) (v 6) (r D) s) →
      Derives Δ (ForcingFreshParentOpening.data (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
        (r L) (r S) (r D) (s 4) (r E) (r ∘ images) u) →
      Derives Δ (ForcingRawModalBody.nestedData 2 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
        (v 2) (v 3) (s 2) (s 3) (u 8) x) →
      Derives Δ (implication test (r w) (r z) (r d) (r H) (x 3)) →
      Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hParent := Derives.conjL hNeg
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
  have hOld := of_eq (ForcingFreshParentOpening.data_rename w z a f A b c d t L S N body Parent images negOpen r) (move hParent)
  have hOldCompiler := of_eq (ForcingNegCode.data_rename Reln w a A f j C N negData r) (move (.conjL (.conjR hNeg)))
  have hOldRun := of_eq (ForcingRawModalBody.data_rename w (negOpen 7) (images 9) A f z d
    (negData 3) (negData 4) (negNodes 1) (negNodes 2) (negOpen 8) negOut r) (move hNegQueries)
  have hOldHead := Derives.conjL hOldCompiler
  have hNewHead := Derives.conjL hDensity
  have eEmpty := OmegaUniversal.empty_unique (r (negData 0)) (v 0) (ZFContext.arithmetic hZ1).base.extensionality
    (.conjL hOldHead) (.conjL hNewHead)
  have hHead := SyntaxVariableImagePoint.code_subst_index true (r w) (r (negData 0)) (r (negData 1)) (v 0)
    eEmpty (.conjL (.conjR hOldHead))
  have eHead := SyntaxVariables.unique hZ1 true (r w) (v 0) (r (negData 1)) (v 1) hw1 hHead (.conjL (.conjR hNewHead))
  have hOldCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOld)))))))
  have hNewCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists (r w) (r (images 8)) (r (images 9)) (r a) (r f)
    (r z) (r d) (r A) (r c) (u 2) (u 3) hLift
  have hList := Derives.conjL hLists
  have ht1 := SyntaxTerms.range hZ1 (r w) (r z) (r d) (r t) hw1 (of_eq (SyntaxTermSyntax.term_rename w z d t r) (move ht))
  have eList := StructuralConsUnique.unique hZ1 (r w) (r t) (r (images 8)) (r (negOpen 7)) (u 7) hw1 ht1
    (.conjL (.conjL (.conjR (.conjR hList)))) hOldCons hNewCons
  have compare (order : Bool) (M O Y Y' : Fin l)
      (hm : Derives Δ (ForcingGuardCode.compiled order Reln (r w) (r A) (r f) (r (negData 1)) M))
      (ho : Derives Δ (ForcingGuardCode.compiled order Reln (r w) (r A) (r f) (v 1) O))
      (hY : Derives Δ (substituted (r w) (r (negOpen 7)) (r (images 9)) (r A) (r f) (r z) (r d) M Y))
      (hY' : Derives Δ (substituted (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) O Y')) :
      Derives Δ (.equal Y Y') := by
    let P := ForcingGuardCode.compiled order Reln (r w).castSucc (r A).castSucc (r f).castSucc (Fin.last l) M.castSucc
    have inst (i : Fin l) : P.instantiate i = ForcingGuardCode.compiled order Reln (r w) (r A) (r f) i M := by
      simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    have hm' := of_eq (inst (v 1)) (.eqSubst P eHead (of_eq (inst (r (negData 1))).symm hm))
    have eq := ForcingGuardCode.unique hZ1 order Reln (r w) (r A) (r f) (v 1) M O hw1 hm' ho
    have hY1 := SyntaxMixedFormulaJudgmentSubst.subst_r (r w) (r (negOpen 7)) (r (images 9))
      (r A) (r f) (r z) (r d) M Y (u 7) eList hY
    exact SyntaxMixedFormulaOutputInduction.unique hZ1 (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) O Y Y'
      hw1 (SyntaxMixedFormulaJudgmentSubst.subst_n (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d) M Y O eq hY1) hY'
  have eM := compare false (r (negData 3)) (v 2) (r (negOut 1)) (x 1)
    (.conjL (.conjR (.conjR hOldCompiler))) (.conjL (.conjR hDensity))
    (.conjL (.conjR (.conjL hOldRun))) (.conjL (.conjR (.conjL hQueryOut)))
  have eO := compare true (r (negData 4)) (v 3) (r (negOut 2)) (x 2)
    (.conjL (.conjR (.conjR (.conjR hOldCompiler)))) (.conjL (.conjR (.conjR hDensity)))
    (.conjL (.conjR (.conjR hOldRun))) (.conjL (.conjR (.conjR hQueryOut)))
  have hOuter := ProjectCompilerUniqueTransport.binary_left 2 (r w) (x 1) (x 0) (u 8) (r (negOut 1))
    (eq_symm eM) (.conjL (.conjL hQueryOut))
  have hInner := ProjectCompilerUniqueTransport.binary_left 2 (r w) (x 2) (x 3) (x 0) (r (negOut 2))
    (eq_symm eO) (.conjL (.conjR hQueryOut))
  have hOuterType := SyntaxMixedFormulaJudgment.target_type (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
    (s 4) (u 8) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))))
  have hInnerType := SyntaxMixedFormulaJudgment.target_type (r w) (u 7) (r (images 9)) (r A) (r f) (r z) (r d)
    (s 3) (x 0) (.conjR (.conjR (.conjL hQueryOut)))
  have hH1 := of_eq (formulaCode_rename w H z d r) (move hH)
  have hY := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) (r H) (r W) (u 8) hw1 hz1 hH1
    (of_eq (formulaCode_rename w W z d r) (move hW)) hOuterType
    (of_eq (implication_rename test w z d H W r) (move hToW)) hp
  have hI := ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r d) (r H) (r (negOut 1)) (x 0) (u 8)
    hw1 hz1 hH1 hOuterType hOuter (of_eq (implication_rename test w z d H (negOut 1) r) (move hM)) hY
  have hTail := ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r d) (r H) (r (negOut 2)) (x 3) (x 0)
    hw1 hz1 hH1 hInnerType hInner (of_eq (implication_rename test w z d H (negOut 2) r) (move hO)) hI
  exact use r v s u x hZ1 move hDensity hShell hOpen hQueryOut hTail

private theorem with_fresh_witness_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B f b c d t L S D E M O rM rO N : Fin m) (nodes : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hc : Derives Γ (successor c z)) (hd : Derives Γ (successor d b))
    (hCode : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z d t))
    (hs : Derives Γ (ForcingDensityCode.shellData w a A B f M O rM rO N D nodes))
    (hQuery : Derives Γ (substituted w L S A f z b (nodes 2) E))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 10 → Fin l)
      (u : Fin 9 → Fin l) (x : Fin 4 → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (r w) (r z) (r A) (r f) (r B) (r b) (r c) (r d) (r t)
        (r L) (r S) (r (nodes 2)) (r (nodes 1)) (r E) v u) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (r w) (u 7) (v 9) (r B) (r f) (r z) (r d)
        (r rM) (r rO) (r N) (r (nodes 0)) (u 8) x) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hIn : Derives Γ (ForcingFreshParentOpening.quantifiedInput false w z A f B b c d t L S (nodes 2) (nodes 1) E) :=
    .conjI hw (.conjI hz (.conjI hB (.conjI hc (.conjI hd (.conjI hCode (.conjI ht
      (.conjI (.conjL (.conjL (.conjR (.conjR hs)))) hQuery)))))))
  have he := ForcingFreshParentOpening.produce_quantified hZ false w z A f B b c d t L S (nodes 2) (nodes 1) E hIn
  refine eliminate_objects hZ 10 (fun r v => ForcingFreshParentOpening.quantifiedAtImages false
    (r w) (r z) (r A) (r f) (r B) (r b) (r c) (r d) (r t) (r L) (r S) (r (nodes 2)) (r (nodes 1)) (r E) v) he out ?_
  intro l Δ r v hZ1 move hImage
  refine eliminate_objects hZ1 9 (fun s u => ForcingFreshParentOpening.quantifiedData false
    (s (r w)) (s (r z)) (s (r A)) (s (r f)) (s (r B)) (s (r b)) (s (r c)) (s (r d)) (s (r t))
    (s (r L)) (s (r S)) (s (r (nodes 2))) (s (r (nodes 1))) (s (r E)) (s ∘ v) u) hImage (out.rename r) ?_
  intro l' Ξ s u hZ2 move2 hOpen
  let p := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename p) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move2 (move h))
  have hS := of_eq (ForcingDensityCode.shellData_rename w a A B f M O rM rO N D nodes p) (carry hs)
  have hU8 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen))))))))
  have hNested := ForcingRawModalBody.nested_from_query hZ2 0 (p w) (u 7) (s (v 9)) (p B) (p f) (p z) (p d)
    (p rM) (p rO) (p N) (p (nodes 0)) (p (nodes 1)) (u 8)
    (of_eq (omega_rename w p) (carry hw)) (.conjL (.conjL (.conjR hS))) (.conjL (.conjL hS)) hU8
  refine eliminate_objects hZ2 4 (fun q x => ForcingRawModalBody.nestedData 0 (q (p w)) (q (u 7)) (q (s (v 9)))
    (q (p B)) (q (p f)) (q (p z)) (q (p d)) (q (p rM)) (q (p rO)) (q (p N)) (q (p (nodes 0))) (q (u 8)) x)
    hNested ((out.rename r).rename s) ?_
  intro l'' Ω q x hZ3 move3 hWitness
  let e := q ∘ p
  have carry0 {F : Formula m} (h : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F p q) (move3 (carry h))
  have hOpen' := of_eq (ForcingFreshParentOpening.quantifiedData_rename false (p w) (p z) (p A) (p f) (p B)
    (p b) (p c) (p d) (p t) (p L) (p S) (p (nodes 2)) (p (nodes 1)) (p E) (s ∘ v) u q) (move3 hOpen)
  exact of_eq ((congrArg (Source.Formula.rename q) (SourceAlgebra.rename_comp out r s)).trans
    (SourceAlgebra.rename_comp out p q)).symm
    (use e (q ∘ s ∘ v) (q ∘ u) x hZ3 carry0 hOpen' hWitness)

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
  refine with_fresh_witness_at hZ2 (p w) (p z) (p a) (p A) (p B) (p f) (p b) (p c) (s d) t
    (p L) (p S) (p D) (p E) (p M) (p O) (p rM) (p rO) (p N) (p ∘ nodes)
    (of_eq (omega_rename w p) (carry hw)) (of_eq (empty_rename z p) (carry hz))
    (of_eq (successor_rename B A p) (carry hB)) (of_eq (successor_rename c z p) (carry hc))
    hD' (.conjL (.conjR hT)) (.conjR (.conjR hT))
    (of_eq (ForcingDensityCode.shellData_rename w a A B f M O rM rO N D nodes p) (carry hs))
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

end PPAC.Migration.ForcingDensityInstantiation
