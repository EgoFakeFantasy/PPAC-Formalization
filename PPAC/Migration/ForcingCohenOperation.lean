/- Pinned AssignedGraphs.Condition.antichain_cardinal_le:407-410.
The actual operation uses the SAME code family, decoder, compatible-choice
and flip graphs. Its totality/uniqueness are proved, not passed to the hull. -/
import PPAC.Migration.ForcingCohenFlip

namespace PPAC.Migration.ForcingCohenOperation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (z C D Q F a f y : M.Carrier .set) : Prop := ∃ b n, PureKuratowski.Code M a b n ∧
  ((b = z ∧ ∃ x, PureKuratowski.PairMember M n x f ∧ PureKuratowski.PairMember M x y F) ∨
   (b ≠ z ∧ ∃ p q g, PureKuratowski.PairMember M f p D ∧ PureKuratowski.PairMember M p q Q ∧
     PureKuratowski.PairMember M q g C ∧ PureKuratowski.PairMember M n y g))

def value {m} (z C D Q F a f y : Project.Term m) : Project.Formula 1 m := .existsE (.existsE (.conj
  (PureKuratowskiProject.convention.code a.weaken.weaken (.bound 1) .newest) (.disj
  (.conj (Project.Formula.extensionalEq (.bound 1) z.weaken.weaken) (.existsE (.conj
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest f.weaken.weaken.weaken)
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention .newest y.weaken.weaken.weaken F.weaken.weaken.weaken))))
  (.conj (.neg (Project.Formula.extensionalEq (.bound 1) z.weaken.weaken))
    (.existsE (.existsE (.existsE (.conj
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention f.weaken.weaken.weaken.weaken.weaken (.bound 2) D.weaken.weaken.weaken.weaken.weaken)
      (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 2) (.bound 1) Q.weaken.weaken.weaken.weaken.weaken)
      (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest C.weaken.weaken.weaken.weaken.weaken)
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 3) y.weaken.weaken.weaken.weaken.weaken .newest)))))))))))

derive_free_closed value

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (z C D Q F a f y : Project.Term m) :
    Project.Formula.satisfies ρ (value z C D Q F a f y) ↔
      Value (z.eval ρ) (C.eval ρ) (D.eval ρ) (Q.eval ρ) (F.eval ρ) (a.eval ρ) (f.eval ρ) (y.eval ρ) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,(KuratowskiZF.interpretation hM).satisfies_code_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Definitional.Term.eval_weaken]
  rfl

theorem value_exists (_hM : FirstOrder.Theory.Models M nativeZF) {z w W P Space C D Q F B L a f : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hQ : MapsTo P P Q) (hF : MapsTo W W F)
    (hL : ForcingCohenCoordinates.Cartesian B w L) (ha : (Project.FirstOrderSemantics.reduct M).mem a L)
    (hf : (Project.FirstOrderSemantics.reduct M).mem f Space) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y W ∧ Value z C D Q F a f y := by
  obtain ⟨b,_,n,hn,ha⟩ := (hL a).mp ha
  classical
  by_cases hb : b = z
  · obtain ⟨x,hx,_⟩ := ((h.1 f).mp hf).1.2 n hn
    obtain ⟨y,hy,_⟩ := hF.1.2 x (((h.1 f).mp hf).2 n x hx)
    exact ⟨y,hF.2 x y hy,b,n,ha,Or.inl ⟨hb,x,hx,hy⟩⟩
  · obtain ⟨p,hp,_⟩ := h.2.2.1.1.2 f hf
    obtain ⟨q,hq,_⟩ := hQ.1.2 p (h.2.2.1.2 f p hp)
    obtain ⟨g,hg,_⟩ := h.2.1.1.2 q (hQ.2 p q hq)
    have hcode := h.2.1.2 q g hg
    obtain ⟨y,hy,_⟩ := hcode.1.1.2 n hn
    exact ⟨y,hcode.1.2 n y hy,b,n,ha,Or.inr ⟨hb,p,q,g,hp,hq,hg,hy⟩⟩

theorem value_unique {z w W P Space C D Q F a f x y : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hQ : MapsTo P P Q) (hF : MapsTo W W F)
    (hf : (Project.FirstOrderSemantics.reduct M).mem f Space)
    (hx : Value z C D Q F a f x) (hy : Value z C D Q F a f y) : x = y := by
  obtain ⟨b,n,ha,hx⟩ := hx
  obtain ⟨b',n',ha',hy⟩ := hy
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ha ha'
  rcases hx with ⟨hb,u,hu,hux⟩ | ⟨hb,p,q,g,hp,hq,hg,hgx⟩ <;>
    rcases hy with ⟨hb',v,hv,hvy⟩ | ⟨hb',p',q',g',hp',hq',hg',hgy⟩
  · have e := function_unique ((h.1 f).mp hf).1 hu hv
    exact function_unique hF.1 hux (e.symm ▸ hvy)
  · exact (hb' hb).elim
  · exact (hb hb').elim
  · have ep := function_unique h.2.2.1.1 hp hp'
    subst p'
    have eq := function_unique hQ.1 hq hq'
    subst q'
    have eg := function_unique h.2.1.1 hg hg'
    subst g'
    exact function_unique (h.2.1.2 q g hg).1.1 hgx hgy

/-- Exact graph, bounded on labels x ALL internal functions w -> W. -/
def Graph (z L Space C D Q F O : M.Carrier .set) : Prop := ∀ a f y,
  (∃ fy, PureKuratowski.Code M fy f y ∧ PureKuratowski.PairMember M a fy O) ↔
    (Project.FirstOrderSemantics.reduct M).mem a L ∧ (Project.FirstOrderSemantics.reduct M).mem f Space ∧
      Value z C D Q F a f y

def graph {m} (z L Space C D Q F O : Project.Term m) : Project.Formula 1 m := .forallE (.forallE (.forallE (.iff
  (ForcingChainBound.rel (𝒞 := PureKuratowskiProject.convention) O.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
  (.conj (.mem (.bound 2) L.weaken.weaken.weaken) (.conj (.mem (.bound 1) Space.weaken.weaken.weaken)
    (value z.weaken.weaken.weaken C.weaken.weaken.weaken D.weaken.weaken.weaken Q.weaken.weaken.weaken
      F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))

derive_free_closed graph

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (z L Space C D Q F O : Project.Term m) :
    Project.Formula.satisfies ρ (graph z L Space C D Q F O) ↔
      Graph (z.eval ρ) (L.eval ρ) (Space.eval ρ) (C.eval ρ) (D.eval ρ) (Q.eval ρ) (F.eval ρ) (O.eval ρ) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    ForcingChainBound.rel_semantics (KuratowskiZF.interpretation hM),value_semantics hM,Definitional.Term.eval_weaken]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {z w W P Space C D Q F B L : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hQ : MapsTo P P Q) (hF : MapsTo W W F)
    (hL : ForcingCohenCoordinates.Cartesian B w L) : ∃ O, Graph z L Space C D Q F O := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨T,hT⟩ := ZF.exists_cartesianProduct hZF I Space W
  obtain ⟨Z,hZ⟩ := ZF.exists_cartesianProduct hZF I L T
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 5 :=
    ((((⟨fun _ => z,fun _ => z⟩ : Env _ 1).push C).push D).push Q).push F
  let φ : Project.UnarySchema 5 := {body := (.existsE (.existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.convention.code (.bound 4) (.bound 3) .newest) (.conj
      (PureKuratowskiProject.convention.code .newest (.bound 2) (.bound 1))
      (value (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1))))))))}
  have hφ t : φ.denote ρ t ↔ ∃ a f y fy, PureKuratowski.Code M t a fy ∧
      PureKuratowski.Code M fy f y ∧ Value z C D Q F a f y := by
    simp only [φ,Project.UnarySchema.denote,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,(KuratowskiZF.interpretation hM).satisfies_code_iff,value_semantics hM]
    rfl
  obtain ⟨O,hO⟩ := ZF.separation_exists_d hZF φ ρ Z
  refine ⟨O,fun a f y => ⟨?_,?_⟩⟩
  · rintro ⟨fy,hfy,t,ht,htO⟩
    obtain ⟨htZ,htφ⟩ := (hO t).mp htO
    obtain ⟨a',f',y',fy',ht',hfy',hv⟩ := (hφ t).mp htφ
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hfy hfy'
    obtain ⟨a'',ha,fy'',hfyT,ht''⟩ := (hZ t).mp htZ
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht''
    obtain ⟨f'',hf,y'',_,hfy''⟩ := (hT fy).mp hfyT
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hfy hfy''
    exact ⟨ha,hf,hv⟩
  · rintro ⟨ha,hf,hv⟩
    obtain ⟨v,hvW,hvv⟩ := value_exists (z := z) hM h hQ hF hL ha hf
    have hyW := value_unique h hQ hF hf hvv hv ▸ hvW
    obtain ⟨fy,hfy⟩ := I.total f y
    obtain ⟨t,ht⟩ := I.total a fy
    exact ⟨fy,hfy,t,ht,(hO t).mpr ⟨(hZ t).mpr ⟨a,ha,fy,(hT fy).mpr ⟨f,hf,y,hyW,hfy⟩,ht⟩,
      (hφ t).mpr ⟨a,f,y,fy,ht,hfy,hv⟩⟩⟩

theorem operation (hM : FirstOrder.Theory.Models M nativeZF) {z w W P Space C D Q F B L O : M.Carrier .set}
    (h : ForcingCohenCodes.Data w W P Space C D) (hQ : MapsTo P P Q) (hF : MapsTo W W F)
    (hL : ForcingCohenCoordinates.Cartesian B w L) (hO : Graph z L Space C D Q F O) :
    ForcingCountableTreeAlgebra.Operation (KuratowskiZF.interpretation hM) w L W O := by
  constructor
  · intro a ha f hf
    have hfS := (h.1 f).mpr ((ForcingSupportSize.native_mapsTo hM w W f).mpr hf)
    obtain ⟨y,hy,hv⟩ := value_exists (z := z) hM h hQ hF hL ha hfS
    exact ⟨y,hy,(hO a f y).mpr ⟨ha,hfS,hv⟩⟩
  · intro a f x y hx hy
    have hx' := (hO a f x).mp hx
    exact value_unique h hQ hF hx'.2.1 hx'.2.2 ((hO a f y).mp hy).2.2

def operationSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (ProjectSyntax.encode id (ForcingCohenCodes.dataFormula (1 : Fin 11) 2 3 4 5 6))
    (.imp (Project.Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound 7) (.bound 3) (.bound 3))
    (.imp (Project.Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound 8) (.bound 2) (.bound 2))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (9 : Fin 11) 1 10))
      (.existsE (.conj (graph (.bound 1) (.bound 11) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest)
        (ForcingCountableTreeAlgebra.operationFormula (𝒞 := PureKuratowskiProject.convention)
          (.bound 2) (.bound 11) (.bound 3) .newest)))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    graph_freeClosed,ForcingCountableTreeAlgebra.operationFormula_freeClosed]

theorem operation_models (hM : FirstOrder.Theory.Models M nativeZF) : (Project.fo_sentence operationSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) operationSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenCodes.data_semantics (M := M),
    ForcingCohenCoordinates.cartesian_semantics (M := M),
    Project.Formula.satisfies_isFunctionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    graph_semantics hM,ForcingCountableTreeAlgebra.operation_semantics (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]
  intro h hQ hF hL
  have hQ' := (ForcingSupportSize.native_mapsTo hM _ _ _).mpr hQ
  have hF' := (ForcingSupportSize.native_mapsTo hM _ _ _).mpr hF
  obtain ⟨O,hO⟩ := exists_graph (z := bound 0) hM h hQ' hF' hL
  exact ⟨O,hO,operation hM h hQ' hF' hL hO⟩

theorem operation_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence operationSentence) :=
  ModelTransfer.derives (fun _ hM => operation_models hM)

end PPAC.Migration.ForcingCohenOperation
