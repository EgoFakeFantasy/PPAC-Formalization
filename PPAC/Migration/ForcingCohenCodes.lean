/- Pinned AssignedGraphs.Condition.exists_code/code_range/enriched_graph_injective:
internal enumeration of the ACTUAL countable condition graph, using the existing
empty/singleton Option representation and existing small-set injection bridge. -/
import PPAC.Migration.ForcingCountableHull
import PPAC.Migration.ForcingWithTopCarrier

namespace PPAC.Migration.ForcingCohenCodes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single Element)
open ForcingSupportSize (MapsTo Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- At a successor index, enumerate the singleton of the corresponding graph entry. -/
def At (J n y : M.Carrier .set) : Prop := ∃ i z,
  (Project.FirstOrderSemantics.reduct M).SuccessorOf n i ∧ PureKuratowski.PairMember M z i J ∧ Single y z

def atFormula {m} (J n y : Project.Term m) : Project.Formula 1 m := .existsE (.existsE (.conj
  (Project.Formula.isSuccessor n.weaken.weaken (.bound 1)) (.conj
  (Project.Formula.orderedPairMem PureKuratowskiProject.convention .newest (.bound 1) J.weaken.weaken)
  (Project.Formula.isSingleton y.weaken.weaken .newest))))
derive_free_closed atFormula

theorem at_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (J n y : Project.Term m) :
    Project.Formula.satisfies ρ (atFormula J n y) ↔ At (J.eval ρ) (n.eval ρ) (y.eval ρ) := by
  simp only [atFormula, At, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isSuccessor_iff, Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_isSingleton_iff (ModelTransfer.extensionality hM), Definitional.Term.eval_weaken]
  rfl

theorem at_unique (hM : FirstOrder.Theory.Models M nativeZF) {w p J n y v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) J p w)
    (hy : At J n y) (hv : At J n v) : y = v := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨i, z, hni, hzi, hy⟩ := hy
  obtain ⟨j, t, hnj, htj, hv⟩ := hv
  have e := Structure.SuccessorOf.predecessor_eq hZF.1
    ((hw.isOrdinal hZF).mem (hJ.1.output_mem_of_pairMember hzi)) hni hnj
  have e' := hJ.2 z t i hzi (e.symm ▸ htj)
  exact ForcingWithTopCarrier.single_unique hM hy (e'.symm ▸ hv)

/-- Range(code p) is EXACTLY none plus all some(graph entries), with no omitted point. -/
def Code (w W p f : M.Carrier .set) : Prop := MapsTo w W f ∧
  ∀ y, (∃ n, PureKuratowski.PairMember M n y f) ↔ Element p y

def code {m} (w W p f : Fin m) : Source.Formula m :=
  (Source.SetLanguage.mapsTo f w W).conj (.all
    ((Source.Formula.ex (Source.SetLanguage.edge f.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)).iff
      (ForcingWithTopCarrier.element p.castSucc (Fin.last m))))

theorem code_semantics {m} (env : Fin m → M.Carrier .set) (w W p f : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (code w W p f) ↔
      Code (env w) (env W) (env p) (env f) := by
  simp only [code, Code, Source.Formula.iff, Source.Formula.Realize, ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingWithTopCarrier.element_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact and_congr_right (fun _ => forall_congr' fun y => ⟨fun h => ⟨h.1,h.2⟩, fun h => ⟨h.mp,h.mpr⟩⟩)

/-- Source exists_code, using only an existing p -> internal omega injection. -/
theorem exists_code (hM : FirstOrder.Theory.Models M nativeZF) {w S W p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hW : ForcingWithTopCarrier.Carrier S W)
    (hpS : (Project.FirstOrderSemantics.reduct M).MemberSubset p S) (hp : Small p w) :
    ∃ f, Code w W p f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨J, hJ⟩ := (ForcingSupportSize.native_small hM p w).mp hp
  obtain ⟨zero, hz, hzw⟩ := hw.1.1
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : Project.BinarySchema 1 := {body := (.disj (atFormula (.bound 2) (.bound 1) .newest)
    (.conj (.neg (.existsE (atFormula (.bound 3) (.bound 2) .newest))) (Project.Formula.isEmpty .newest)))}
  have hφ n y : φ.denote ρ n y ↔ At J n y ∨ ((¬ ∃ v, At J n v) ∧ Empty y) := by
    simp only [φ, Project.BinarySchema.denote, Project.Formula.satisfies_disj_iff, at_semantics hM,
      Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_neg_iff,
      Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_isEmpty_iff]
    rfl
  obtain ⟨f, hf, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := w) (target := W)
    (by
      intro n _
      classical
      by_cases h : ∃ y, At J n y
      · obtain ⟨y, hy⟩ := h
        exact ⟨y, (hφ n y).mpr (Or.inl hy)⟩
      · exact ⟨zero, (hφ n zero).mpr (Or.inr ⟨h,hz⟩)⟩)
    (by
      intro n _ y v hy hv
      rcases (hφ n y).mp hy with hy | hy <;> rcases (hφ n v).mp hv with hv | hv
      · exact at_unique hM hw hJ hy hv
      · exact (hv.1 ⟨y,hy⟩).elim
      · exact (hy.1 ⟨v,hv⟩).elim
      · exact ForcingWithTopCarrier.empty_unique hM hy.2 hv.2)
    (by
      intro n y _ hy
      apply (hW y).mpr
      rcases (hφ n y).mp hy with ⟨i,z,_,hzi,hy⟩ | ⟨_,hy⟩
      · exact Or.inr ⟨z,hpS z (hJ.1.input_mem_of_pairMember hzi),hy⟩
      · exact Or.inl hy)
  refine ⟨f, (ForcingSupportSize.native_mapsTo hM w W f).mpr hf, fun y => ⟨?_,?_⟩⟩
  · rintro ⟨n,hny⟩
    rcases (hφ n y).mp ((he n y).mp hny).2 with ⟨i,z,_,hzi,hy⟩ | ⟨_,hy⟩
    · exact Or.inr ⟨z,hJ.1.input_mem_of_pairMember hzi,hy⟩
    · exact Or.inl hy
  · rintro (hy | ⟨z,hzp,hy⟩)
    · refine ⟨zero, (he zero y).mpr ⟨hzw,(hφ zero y).mpr (Or.inr ⟨?_,hy⟩)⟩⟩
      rintro ⟨v,i,z,hi,_,_⟩
      exact hz i hi.predecessor_mem
    · obtain ⟨i,hi,hzi⟩ := hJ.1.2.2 z hzp
      obtain ⟨n,hni,hn⟩ := hw.1.2 i hi
      exact ⟨n,(he n y).mpr ⟨hn,(hφ n y).mpr (Or.inl ⟨i,z,hni,hzi,hy⟩)⟩⟩

/-- No condition functionality is needed: Option enrichment recovers the entire graph. -/
theorem enriched_graph_injective (hM : FirstOrder.Theory.Models M nativeZF) {p q : M.Carrier .set}
    (h : ∀ y, Element p y ↔ Element q y) : p = q := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro z
  obtain ⟨y,hy⟩ := ForcingWithTopCarrier.exists_single hM z
  have forward {p q : M.Carrier .set} (h : ∀ y, Element p y ↔ Element q y)
      (hz : (Project.FirstOrderSemantics.reduct M).mem z p) : (Project.FirstOrderSemantics.reduct M).mem z q := by
    rcases (h y).mp (Or.inr ⟨z,hz,hy⟩) with he | ⟨t,ht,hyt⟩
    · exact (ForcingWithTopCarrier.single_nonempty hy he).elim
    · exact (ForcingWithTopCarrier.single_injective hyt hy) ▸ ht
  exact ⟨forward h, forward (fun y => (h y).symm)⟩

theorem code_injective (hM : FirstOrder.Theory.Models M nativeZF) {w W p q f : M.Carrier .set}
    (hp : Code w W p f) (hq : Code w W q f) : p = q :=
  enriched_graph_injective hM (fun y => (hp.2 y).symm.trans (hq.2 y))

/-- Decode relation preserves the given condition whenever its exact code is supplied. -/
def Decode (w W P f p : M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).mem p P ∧ Code w W p f) ∨
  ((¬ ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ Code w W q f) ∧ Empty p)

def decode {m} (w W P f p : Fin m) : Source.Formula m :=
  ((Source.Formula.mem p P).conj (code w W p f)).disj
  ((Source.Formula.neg (.ex ((Source.Formula.mem (Fin.last m) P.castSucc).conj
    (code w.castSucc W.castSucc (Fin.last m) f.castSucc)))).conj (ForcingWithTopCarrier.empty p))

theorem decode_semantics {m} (env : Fin m → M.Carrier .set) (w W P f p : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (decode w W P f p) ↔
      Decode (env w) (env W) (env P) (env f) (env p) := by
  simp only [decode, Decode, Source.Formula.Realize, code_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decode_code (hM : FirstOrder.Theory.Models M nativeZF) {w W P p f q : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hc : Code w W p f)
    (hd : Decode w W P f q) : q = p := by
  rcases hd with ⟨_,hq⟩ | ⟨hn,_⟩
  · exact code_injective hM hq hc
  · exact (hn ⟨p,hp,hc⟩).elim

def codeBody : Source.Formula 4 :=
  (ForcingWithTopCarrier.carrier 0 2).imp ((Source.SetLanguage.subset 3 0).imp
    ((ForcingSupportSize.small 3 1).imp (.ex (code (1 : Fin 4).castSucc (2 : Fin 4).castSucc
      (3 : Fin 4).castSucc (Fin.last 4)))))

def codeSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4 (.imp (Project.Formula.isOmega (.bound 1))
    (ProjectSyntax.encode id codeBody))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem code_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence codeSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) codeSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM)]
  intro hw
  simp only [codeBody, Source.Formula.Realize,ForcingWithTopCarrier.carrier_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    code_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact fun hW hpS hp => exists_code hM hw hW hpS hp

theorem code_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence codeSentence) :=
  ModelTransfer.derives (fun _ hM => code_models hM)

/-- One internal function selecting exact codes for ALL actual conditions. -/
def Family (w W P C : M.Carrier .set) : Prop := ForcingConditionGraphs.FunctionOn P C ∧
  ∀ p f, PureKuratowski.PairMember M p f C → Code w W p f

def family {m} (w W P C : Fin m) : Source.Formula m :=
  (Source.SetLanguage.functionOn C P).conj (.all (.all
    ((Source.SetLanguage.edge C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (code w.castSucc.castSucc W.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem family_semantics {m} (env : Fin m → M.Carrier .set) (w W P C : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (family w W P C) ↔
      Family (env w) (env W) (env P) (env C) := by
  simp only [family,Family,Source.Formula.Realize,ForcingConditionGraphs.functionOn_semantics (M := M),
    KuratowskiZF.source_edge,code_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem family_injective (hM : FirstOrder.Theory.Models M nativeZF) {w W P C p q f : M.Carrier .set}
    (hC : Family w W P C) (hp : PureKuratowski.PairMember M p f C) (hq : PureKuratowski.PairMember M q f C) : p = q :=
  code_injective hM (hC.2 p f hp) (hC.2 q f hq)

theorem family_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w S W P Space : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : ForcingWithTopCarrier.Carrier S W)
    (hP : ForcingCohenConditions.Carrier S w P)
    (hSpace : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) Space w W) :
    ∃ C, Family w W P C := by
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 2 := (⟨fun _ => w,fun _ => w⟩ : Env _ 1).push W
  let φ : Project.BinarySchema 2 := {body := ProjectSyntax.encode Fin.rev (code (0 : Fin 4) 1 2 3), freeClosed := ProjectSyntax.freeClosed _ _}
  have hφ p f : φ.denote ρ p f ↔ Code w W p f := by
    rw [Project.BinarySchema.denote,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM)]
    exact code_semantics _ (0 : Fin 4) 1 2 3
  obtain ⟨C,hC,he⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM) hZFC φ ρ
    (X := P) (Y := Space) (by
      intro p hp
      have hcond := (hP p).mp hp
      obtain ⟨f,hf⟩ := exists_code hM hw hW hcond.1 hcond.2.2
      exact ⟨f,(hSpace f).mpr ((ForcingSupportSize.native_mapsTo hM w W f).mp hf.1),(hφ p f).mpr hf⟩)
  exact ⟨C,((ForcingSupportSize.native_mapsTo hM P Space C).mpr hC).1,
    fun p f hf => (hφ p f).mp (he p f hf)⟩

theorem empty_condition (hM : FirstOrder.Theory.Models M nativeZF) {S w z : M.Carrier .set}
    (hz : Empty z) : ForcingCohenConditions.Condition S w z := by
  refine ⟨fun p hp => (hz p hp).elim,?_,ForcingSupportSize.small_empty hM w hz⟩
  intro x y v hy _
  obtain ⟨p,_,hp⟩ := hy
  exact (hz p hp).elim

theorem decode_exists (hM : FirstOrder.Theory.Models M nativeZF) {S w W P f : M.Carrier .set}
    (hP : ForcingCohenConditions.Carrier S w P) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p P ∧ Decode w W P f p := by
  classical
  by_cases h : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p P ∧ Code w W p f
  · obtain ⟨p,hp,hc⟩ := h
    exact ⟨p,hp,Or.inl ⟨hp,hc⟩⟩
  · obtain ⟨z,hz⟩ := ForcingWithTopCarrier.exists_empty hM
    exact ⟨z,(hP z).mpr (empty_condition hM hz),Or.inr ⟨h,hz⟩⟩

theorem decode_unique (hM : FirstOrder.Theory.Models M nativeZF) {w W P f p q : M.Carrier .set}
    (hp : Decode w W P f p) (hq : Decode w W P f q) : p = q := by
  rcases hp with ⟨hp,hc⟩ | ⟨hn,hp⟩ <;> rcases hq with ⟨hq,hd⟩ | ⟨hm,hq⟩
  · exact code_injective hM hc hd
  · exact (hm ⟨p,hp,hc⟩).elim
  · exact (hn ⟨q,hq,hd⟩).elim
  · exact ForcingWithTopCarrier.empty_unique hM hp hq

theorem decoder_exists (hM : FirstOrder.Theory.Models M nativeZF) {S w W P Space : M.Carrier .set}
    (hP : ForcingCohenConditions.Carrier S w P) :
    ∃ D, MapsTo Space P D ∧ ∀ f p, PureKuratowski.PairMember M f p D → Decode w W P f p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 3 := ((⟨fun _ => w,fun _ => w⟩ : Env _ 1).push W).push P
  let φ : Project.BinarySchema 3 := {body := ProjectSyntax.encode Fin.rev (decode (0 : Fin 5) 1 2 3 4), freeClosed := ProjectSyntax.freeClosed _ _}
  have hφ f p : φ.denote ρ f p ↔ Decode w W P f p := by
    rw [Project.BinarySchema.denote,GodelDefRecursion.encode_semantics hZF.1]
    exact decode_semantics _ (0 : Fin 5) 1 2 3 4
  obtain ⟨D,hD,he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Space) (target := P)
    (by
      intro f _
      obtain ⟨p,_,hp⟩ := decode_exists hM hP
      exact ⟨p,(hφ f p).mpr hp⟩)
    (fun f _ p q hp hq => decode_unique hM ((hφ f p).mp hp) ((hφ f q).mp hq))
    (by
      intro f p _ hp
      rcases (hφ f p).mp hp with ⟨hp,_⟩ | ⟨_,hp⟩
      · exact hp
      · exact (hP p).mpr (empty_condition hM hp))
  exact ⟨D,(ForcingSupportSize.native_mapsTo hM Space P D).mpr hD,
    fun f p hp => (hφ f p).mp ((he f p).mp hp).2⟩

/-- Full internal code/decode data on the actual condition carrier and function space. -/
def Data (w W P Space C D : M.Carrier .set) : Prop :=
  (∀ f, (Project.FirstOrderSemantics.reduct M).mem f Space ↔ MapsTo w W f) ∧
  Family w W P C ∧ MapsTo Space P D ∧
  ∀ f p, PureKuratowski.PairMember M f p D → Decode w W P f p

def dataFormula {m} (w W P Space C D : Fin m) : Source.Formula m :=
  (Source.Formula.all ((Source.Formula.mem (Fin.last m) Space.castSucc).iff
    (Source.SetLanguage.mapsTo (Fin.last m) w.castSucc W.castSucc))).conj
  ((family w W P C).conj ((Source.SetLanguage.mapsTo D Space P).conj (.all (.all
    ((Source.SetLanguage.edge D.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (decode w.castSucc.castSucc W.castSucc.castSucc P.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))))

theorem data_semantics {m} (env : Fin m → M.Carrier .set) (w W P Space C D : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (dataFormula w W P Space C D) ↔
      Data (env w) (env W) (env P) (env Space) (env C) (env D) := by
  simp only [dataFormula,Data,Source.Formula.Realize,Source.Formula.iff,ForcingSupportSize.mapsTo_semantics (M := M),
    family_semantics (M := M),decode_semantics (M := M),KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact and_congr (forall_congr' fun f => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩) Iff.rfl

theorem data_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {w S W P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : ForcingWithTopCarrier.Carrier S W)
    (hP : ForcingCohenConditions.Carrier S w P) : ∃ Space C D, Data w W P Space C D := by
  obtain ⟨Space,hSpace⟩ := SetTheory.ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) w W
  obtain ⟨C,hC⟩ := family_exists hM hZFC hw hW hP hSpace
  obtain ⟨D,hD,hd⟩ := decoder_exists (Space := Space) hM hP
  exact ⟨Space,C,D,(fun f => (hSpace f).trans (ForcingSupportSize.native_mapsTo hM w W f).symm),hC,hD,hd⟩

theorem data_decode_code (hM : FirstOrder.Theory.Models M nativeZF) {w W P Space C D p f q : M.Carrier .set}
    (h : Data w W P Space C D) (hc : PureKuratowski.PairMember M p f C)
    (hd : PureKuratowski.PairMember M f q D) : q = p :=
  decode_code hM (ForcingConditionGraphs.function_input h.2.1.1 hc) (h.2.1.2 p f hc) (h.2.2.2 f q hd)

def dataBody : Source.Formula 4 :=
  (ForcingWithTopCarrier.carrier 0 2).imp ((ForcingCohenConditions.carrier 0 1 3).imp
    (.ex (.ex (.ex (dataFormula (1 : Fin 4).castSucc.castSucc.castSucc
      (2 : Fin 4).castSucc.castSucc.castSucc (3 : Fin 4).castSucc.castSucc.castSucc
      (Fin.last 4).castSucc.castSucc (Fin.last 5).castSucc (Fin.last 6))))))

def dataSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4 (.imp (Project.Formula.isOmega (.bound 1))
    (ProjectSyntax.encode id dataBody))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem data_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence dataSentence := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM)]
  intro hw
  simp only [dataBody,Source.Formula.Realize,ForcingWithTopCarrier.carrier_semantics (M := M),
    ForcingCohenConditions.carrier_semantics (M := M),data_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact fun hW hP => data_exists hM hZFC hw hW hP

/-- Object choice for the whole code family is discharged by the EXISTING internal L. -/
theorem data_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative dataSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact data_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

end PPAC.Migration.ForcingCohenCodes
