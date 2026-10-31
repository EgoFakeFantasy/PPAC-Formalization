/- Pinned CellTowers.stepCell: a single complete cell at each active stage,
independent of the queried word. Consumer: global dependencies and restrictions.
Reuse the existing internal Jensen least-element and functional-image proofs. -/
import PPAC.Migration.ConstructionStepCell

namespace PPAC.Migration.ConstructionStepCellSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFirstAppearance (Cover NewAt Timeline)
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid)
open ConstructionTowerTransitions (Matrix)
open ForcingConditionGraphs (FunctionOn function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Candidate (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one V GV unitV I R S i cell : M.Carrier .set) : Prop :=
  ∃ j D T, Cover I R i j ∧ PureKuratowski.PairMember M i D S ∧
    PureKuratowski.PairMember M j T S ∧ D ≠ T ∧
    ConstructionStepCell.Data hM w zero one V GV unitV D T cell

def Picked (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one V GV unitV I R S i cell : M.Carrier .set) : Prop :=
  (Candidate hM w zero one V GV unitV I R S i cell ∧
    ∀ other, Candidate hM w zero one V GV unitV I R S i other →
      ¬ InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M) other cell) ∨
  (¬ ∃ other, Candidate hM w zero one V GV unitV I R S i other) ∧ cell = zero

def Graph (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one V GV unitV I R S cells : M.Carrier .set) : Prop :=
  FunctionOn I cells ∧ ∀ i cell, PureKuratowski.PairMember M i cell cells ↔
    (Project.FirstOrderSemantics.reduct M).mem i I ∧ Picked hM w zero one V GV unitV I R S i cell

/-- ALL words first appearing at i read the SAME cell and local dependency graph. -/
def AtNew (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one V GV unitV I R S cells : M.Carrier .set) : Prop :=
  ∀ i x, NewAt I R S i x → ∃ cell j D T deps,
    PureKuratowski.PairMember M i cell cells ∧ Cover I R i j ∧
    PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧ D ≠ T ∧
    ConstructionStepCell.Data hM w zero one V GV unitV D T cell ∧
    ConstructionStepCell.DependencyField zero cell deps ∧
    ConstructionCountableConservativeHull.Dependencies w T deps ∧
    (Project.FirstOrderSemantics.reduct M).mem x T ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem x D

def candidate {m : Nat} (w zero one V GV unitV I R S i cell : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ConstructionFirstAppearance.cover I.succ.succ.succ R.succ.succ.succ i.succ.succ.succ 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ i.succ.succ.succ 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ 2 0)) (.conj (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0))) (ConstructionStepCell.data w.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ V.succ.succ.succ GV.succ.succ.succ unitV.succ.succ.succ 1 0 cell.succ.succ.succ))))))))

theorem candidate_freeClosed {m : Nat} (w zero one V GV unitV I R S i cell : Fin m) :
    (candidate w zero one V GV unitV I R S i cell).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionStepCell.data_freeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV I R S i cell : Fin m) :
    Project.Formula.satisfies env (candidate w zero one V GV unitV I R S i cell) ↔ Candidate hM (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound I) (env.bound R) (env.bound S) (env.bound i) (env.bound cell) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionFirstAppearance.cover_semantics hM,ConstructionStepCell.data_semantics hM]
  rfl

def picked {m : Nat} (w zero one V GV unitV I R S i cell : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (candidate w zero one V GV unitV I R S i cell) (.forallE (.imp (candidate w.succ zero.succ one.succ V.succ GV.succ unitV.succ I.succ R.succ S.succ i.succ 0) (.neg (InnerModel.js_less_m (.bound 0) (.bound cell.succ)))))) (.conj (.neg (.existsE (candidate w.succ zero.succ one.succ V.succ GV.succ unitV.succ I.succ R.succ S.succ i.succ 0))) (Project.Formula.extensionalEq (.bound cell) (.bound zero))))

theorem picked_freeClosed {m : Nat} (w zero one V GV unitV I R S i cell : Fin m) :
    (picked w zero one V GV unitV I R S i cell).FreeClosed := by
  simp -implicitDefEqProofs [picked,Definitional.Formula.FreeClosed,candidate_freeClosed,InnerModel.js_less_m_freeClosed,Project.Formula.extensionalEq]

theorem picked_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV I R S i cell : Fin m) :
    Project.Formula.satisfies env (picked w zero one V GV unitV I R S i cell) ↔ Picked hM (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound I) (env.bound R) (env.bound S) (env.bound i) (env.bound cell) := by
  simp only [picked,Picked,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_disj_iff,Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),candidate_semantics hM,InnerModel.js_less_formula_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))]
  rfl

def graph {m : Nat} (w zero one V GV unitV I R S cells : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn cells I)) (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound I.succ.succ)) (picked w.succ.succ zero.succ.succ one.succ.succ V.succ.succ GV.succ.succ unitV.succ.succ I.succ.succ R.succ.succ S.succ.succ 1 0))))))

theorem graph_freeClosed {m : Nat} (w zero one V GV unitV I R S cells : Fin m) :
    (graph w zero one V GV unitV I R S cells).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,picked_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV I R S cells : Fin m) :
    Project.Formula.satisfies env (graph w zero one V GV unitV I R S cells) ↔ Graph hM (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound I) (env.bound R) (env.bound S) (env.bound cells) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),picked_semantics hM]
  rfl

def atNew {m : Nat} (w zero one V GV unitV I R S cells : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ConstructionFirstAppearance.newAt I.succ.succ R.succ.succ S.succ.succ 1 0) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ.succ.succ.succ.succ.succ 6 4)) (.conj (ConstructionFirstAppearance.cover I.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ 6 3) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ 6 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ 3 1)) (.conj (.neg (Project.Formula.extensionalEq (.bound 2) (.bound 1))) (.conj (ConstructionStepCell.data w.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ 2 1 4) (.conj (ConstructionStepCell.dependencyField zero.succ.succ.succ.succ.succ.succ.succ 4 0) (.conj (ConstructionCountableConservativeHull.dependencies w.succ.succ.succ.succ.succ.succ.succ 1 0) (.conj (.mem (.bound 5) (.bound 1)) (.neg (.mem (.bound 5) (.bound 2))))))))))))))))))))

theorem atNew_freeClosed {m : Nat} (w zero one V GV unitV I R S cells : Fin m) :
    (atNew w zero one V GV unitV I R S cells).FreeClosed := by
  simp -implicitDefEqProofs [atNew,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionStepCell.data_freeClosed,ConstructionStepCell.dependencyField_freeClosed,ConstructionCountableConservativeHull.dependencies_freeClosed,Project.Formula.extensionalEq]

theorem atNew_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one V GV unitV I R S cells : Fin m) :
    Project.Formula.satisfies env (atNew w zero one V GV unitV I R S cells) ↔ AtNew hM (env.bound w) (env.bound zero) (env.bound one) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound I) (env.bound R) (env.bound S) (env.bound cells) := by
  simp only [atNew,AtNew,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionFirstAppearance.newAt_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionStepCell.data_semantics hM,ConstructionStepCell.dependencyField_semantics hM,ConstructionCountableConservativeHull.dependencies_semantics hM]
  rfl

theorem picked_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w zero one V GV unitV I R S i x y : M.Carrier .set}
    (hx : Picked hM w zero one V GV unitV I R S i x) (hy : Picked hM w zero one V GV unitV I R S i y) : x = y := by
  rcases hx with ⟨hx,hxmin⟩ | ⟨hnx,rfl⟩
  · rcases hy with ⟨hy,hymin⟩ | ⟨hny,_⟩
    · rcases hOrder.2.2.1 x y with he | hxy | hyx
      · exact he
      · exact False.elim (hymin x hx hxy)
      · exact False.elim (hxmin y hy hyx)
    · exact False.elim (hny ⟨x,hx⟩)
  · rcases hy with ⟨hy,_⟩ | ⟨_,rfl⟩
    · exact False.elim (hnx ⟨y,hy⟩)
    · rfl

theorem picked_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (w zero one V GV unitV I R S i : M.Carrier .set) : ∃ cell, Picked hM w zero one V GV unitV I R S i cell := by
  classical
  let schema : Project.UnarySchema 10 := {
    body := candidate 1 2 3 4 5 6 7 8 9 10 0
    freeClosed := candidate_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 10 := {
    bound := (Fin.cases w (Fin.cases zero (Fin.cases one (Fin.cases V (Fin.cases GV (Fin.cases unitV (Fin.cases I (Fin.cases R (Fin.cases S (fun _ => i))))))))))
    free := fun _ => zero }
  have he cell : schema.denote env cell ↔ Candidate hM w zero one V GV unitV I R S i cell :=
    candidate_semantics hM (env.push cell) 1 2 3 4 5 6 7 8 9 10 0
  by_cases hn : ∃ cell, Candidate hM w zero one V GV unitV I R S i cell
  · obtain ⟨cell,hCell,hMin⟩ := ConstructionRoundSelection.least_denote hM hOrder schema env
      (by obtain ⟨cell,hCell⟩ := hn; exact ⟨cell,(he cell).mpr hCell⟩)
    exact ⟨cell,Or.inl ⟨(he cell).mp hCell,fun other hOther => hMin other ((he other).mpr hOther)⟩⟩
  · exact ⟨zero,Or.inr ⟨hn,rfl⟩⟩

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (w zero one V GV unitV I R S : M.Carrier .set) :
    ∃ cells, Graph hM w zero one V GV unitV I R S cells := by
  let schema : Project.BinarySchema 9 := {
    body := picked 2 3 4 5 6 7 8 9 10 1 0
    freeClosed := picked_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases zero (Fin.cases one (Fin.cases V (Fin.cases GV
      (Fin.cases unitV (Fin.cases I (Fin.cases R (fun _ => S))))))))
    free := fun _ => zero }
  have he i cell : schema.denote env i cell ↔ Picked hM w zero one V GV unitV I R S i cell :=
    picked_semantics hM ((env.push i).push cell) 2 3 4 5 6 7 8 9 10 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∃ cell, schema.denote env i cell := by
    intro i _
    obtain ⟨cell,hCell⟩ := picked_total hM hOrder w zero one V GV unitV I R S i
    exact ⟨cell,(he i cell).mpr hCell⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∀ a b,
      schema.denote env i a → schema.denote env i b → a = b :=
    fun _ _ _ _ ha hb => picked_unique hM hOrder ((he _ _).mp ha) ((he _ _).mp hb)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env I ht hu
  obtain ⟨cells,hCells,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF
    (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i cell hi hc => (hA cell).mpr ⟨i,hi,hc⟩)
  exact ⟨cells,((ForcingSupportSize.native_mapsTo hM I A cells).mpr hCells).1,
    fun i cell => (hGraph i cell).trans (and_congr_right fun _ => he i cell)⟩

/-- Read the already selected record; no choice depending on x. -/
theorem at_new (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV unitV I R S cells i x : M.Carrier .set}
    (hR : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) R I)
    (hS : FunctionOn I S) (hc : Graph hM w zero one V GV unitV I R S cells)
    (hn : ∃ cell, Candidate hM w zero one V GV unitV I R S i cell)
    (hx : NewAt I R S i x) :
    ∃ cell j D T deps, PureKuratowski.PairMember M i cell cells ∧ Cover I R i j ∧
      PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧ D ≠ T ∧
      ConstructionStepCell.Data hM w zero one V GV unitV D T cell ∧
      ConstructionStepCell.DependencyField zero cell deps ∧
      ConstructionCountableConservativeHull.Dependencies w T deps ∧
      (Project.FirstOrderSemantics.reduct M).mem x T ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem x D := by
  obtain ⟨cell,hCell,_⟩ := hc.1.2 i hx.1
  have hp := ((hc.2 i cell).mp hCell).2
  have hCandidate : Candidate hM w zero one V GV unitV I R S i cell := by
    rcases hp with ⟨h,_⟩ | ⟨h,_⟩
    · exact h
    · exact (h hn).elim
  obtain ⟨j,D,T,hij,hD,hT,hne,hData⟩ := hCandidate
  obtain ⟨deps,hField,hDeps⟩ := ConstructionStepCell.dependencies hM hData
  obtain ⟨_,k,hik,⟨T',hT',hxT'⟩,hnot⟩ := hx
  have hjk : j = k := by
    rcases ConstructionFirstAppearance.cover_le hM hR hij hik.2.1 hik.2.2.1 with he | hlt
    · exact he
    · exact (hik.2.2.2 j hij.2.1 hij.2.2.1 hlt).elim
  subst k
  have hTT : T' = T := function_unique hS hT' hT
  subst T'
  exact ⟨cell,j,D,T,deps,hCell,hij,hD,hT,hne,hData,hField,hDeps,hxT',fun hxD => hnot ⟨D,hD,hxD⟩⟩

theorem assembly (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q values top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : M.Carrier .set}
    (hv : Valid hM w Q values top D mul e mark H C B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) :
    ∃ cells, Graph hM w zero one V GV unitV I R S cells ∧
      AtNew hM w zero one V GV unitV I R S cells := by
  obtain ⟨cells,hCells⟩ := exists_graph hM hOrder w zero one V GV unitV I R S
  refine ⟨cells,hCells,?_⟩
  intro i x hx
  have hn : ∃ cell, Candidate hM w zero one V GV unitV I R S i cell := by
    obtain ⟨_,j,hij,⟨T,hT,hxT⟩,hnot⟩ := hx
    obtain ⟨D,hD,_⟩ := hg.1.2 i hij.1
    have hne : D ≠ T := fun he => hnot ⟨D,hD,he.symm ▸ hxT⟩
    have hStep := ConstructionFlatAttachments.cover_step hM hv hindex hf hr ht hd hg hij hD hT
    obtain ⟨cell,hData⟩ := ConstructionStepCell.from_step hM hOrder ht hStep hne
    exact ⟨cell,j,D,T,hij,hD,hT,hne,hData⟩
  exact at_new hM hd.2.2.2.2.2.2.1 hg.1 hCells hn hx

def assemblySentence {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q values top D mul e mark H C B history)
    (.imp (ConstructionSaturationIndex.data w mu kappa B)
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa traces)
    (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R)
    (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S)
    (.existsE (.conj (graph w.succ zero.succ one.succ V.succ GV.succ unitV.succ I.succ R.succ S.succ 0) (atNew w.succ zero.succ one.succ V.succ GV.succ unitV.succ I.succ R.succ S.succ 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed,graph_freeClosed,atNew_freeClosed]

theorem assembly_models {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionTowerValidity.valid_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM,graph_semantics hM,atNew_semantics hM]
  exact assembly hM hOrder

theorem assembly_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) (assemblySentence w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S)).mp
    (assembly_models w Q values top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces Indices A r I R S (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top D mul e mark H C zero one u K mu B history P outerF kappa
      V mulV unitV markV HV CV terminalLegs baseV : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top D mul e mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top D mul e mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) :
    ∃ traces Indices A r I R S ODomains OE OImages bottom cells,
      ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces ∧
      ConstructionBlockIndex.Data hM kappa traces Indices A r I R ∧
      ConstructionFlatStages.Result history outerF kappa V zero traces I S ∧
      ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages ∧
      ConstructionFlatOuter.Bottoms kappa zero S OImages ∧ ConstructionFlatOuter.Covers V I R S ∧
      Timeline hM V I R bottom S ∧
      ConstructionFlatAttachments.Steps hM w Q values top zero one traces V mulV unitV I R S ∧
      Graph hM w zero one V mulV unitV I R S cells ∧ AtNew hM w zero one V mulV unitV I R S cells := by
  obtain ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,ht,hd,hS,ho,hb,hcovers,hTimeline,hSteps⟩ :=
    ConstructionFlatAttachments.construction hM hOrder hChoice hctx hrec hindex hf hr
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  obtain ⟨cells,hCells,hNew⟩ := assembly hM hOrder hv hindex hf hr ht hd hS.1
  exact ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,cells,ht,hd,hS,ho,hb,hcovers,hTimeline,hSteps,hCells,hNew⟩

def constructionSentence {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q values top D mul e mark H C zero one u K mu B) (.imp (ConstructionSaturationIteration.recursive w Q values top D mul e mark H C zero one K mu B B history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V mulV unitV markV HV CV terminalLegs baseV kappa) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBlockTraces.family w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11) (.conj (ConstructionBlockIndex.data kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 9 8 7 6) (.conj (ConstructionFlatStages.result history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 7 5) (.conj (ConstructionBlockContinuity.outerData B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ outerF.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ terminalLegs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 3 2) (.conj (ConstructionFlatOuter.bottoms kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 2) (.conj (ConstructionFlatOuter.covers V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5) (.conj (ConstructionFirstAppearance.timeline V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 1 5) (.conj (ConstructionFlatAttachments.steps w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ values.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5) (.conj (graph w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 0) (atNew w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mulV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 0)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.result_freeClosed,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFlatOuter.bottoms_freeClosed,ConstructionFlatOuter.covers_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFlatAttachments.steps_freeClosed,graph_freeClosed,atNew_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {m : Nat}
    (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : (Project.fo_sentence (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.result_semantics hM,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFlatOuter.bottoms_semantics hM,ConstructionFlatOuter.covers_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFlatAttachments.steps_semantics hM,graph_semantics hM,atNew_semantics hM]
  exact construction hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q values top D mul e mark H C zero one u K mu B history P outerF kappa V mulV unitV markV HV CV terminalLegs baseV)

end PPAC.Migration.ConstructionStepCellSelection
