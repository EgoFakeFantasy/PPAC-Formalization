/- Pinned ProbeWords.Path factor/terminal: internal graphs, not host choices.
The original left-cancellative monoid and bounded increasing path remain inputs. -/
import PPAC.Migration.ConstructionBaseCostBound

namespace PPAC.Migration.ConstructionProbePath
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_unique function_input)
open ForcingSupportSize (MapsTo)
open ConstructionFractionOrder (NatLe nat_compare)
open ConstructionBaseCostBound (natLeF natLeF_freeClosed natLeF_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Factor (D mul node i j f : M.Carrier .set) : Prop :=
  ∃ ni nj, PureKuratowski.PairMember M i ni node ∧ PureKuratowski.PairMember M j nj node ∧
    (Project.FirstOrderSemantics.reduct M).mem f D ∧ Product mul ni f nj

def Terminal (D mul node a i t : M.Carrier .set) : Prop :=
  ∃ ni, PureKuratowski.PairMember M i ni node ∧ (Project.FirstOrderSemantics.reduct M).mem t D ∧ Product mul ni t a

def Path (w D mul e zero a node : M.Carrier .set) : Prop :=
  MapsTo w D node ∧ (Project.FirstOrderSemantics.reduct M).mem a D ∧ PureKuratowski.PairMember M zero e node ∧
    (∀ i j, (Project.FirstOrderSemantics.reduct M).mem i w → (Project.FirstOrderSemantics.reduct M).mem j w →
      NatLe i j → ∃ f, Factor D mul node i j f) ∧
    (∀ i, (Project.FirstOrderSemantics.reduct M).mem i w → ∃ t, Terminal D mul node a i t)

theorem factor_unique {w D mul e node i j f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hf : Factor D mul node i j f) (hg : Factor D mul node i j g) : f = g := by
  obtain ⟨ni,nj,hi,hj,hfD,hf⟩ := hf
  obtain ⟨ni',nj',hi',hj',hgD,hg⟩ := hg
  have ei := function_unique hn.1 hi' hi
  have ej := function_unique hn.1 hj' hj
  subst ni'; subst nj'
  exact (hm.2.1 ni (hn.2 i ni hi)).2.2 f g nj hfD hgD hf hg

theorem terminal_unique {w D mul e node a i f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hf : Terminal D mul node a i f) (hg : Terminal D mul node a i g) : f = g := by
  obtain ⟨ni,hi,hfD,hf⟩ := hf
  obtain ⟨ni',hi',hgD,hg⟩ := hg
  have ei := function_unique hn.1 hi' hi
  subst ni'
  exact (hm.2.1 ni (hn.2 i ni hi)).2.2 f g a hfD hgD hf hg

theorem factor_self {w D mul e node i : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w) : Factor D mul node i i e := by
  obtain ⟨ni,hni,_⟩ := hn.1.2 i hi
  exact ⟨ni,ni,hni,hni,hm.1.1,((hm.1.2 ni (hn.2 i ni hni) ni).2).mpr rfl⟩

theorem factor_trans {w D mul e node i j k f g h : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hf : Factor D mul node i j f) (hg : Factor D mul node j k g) (hh : Product mul f g h) :
    Factor D mul node i k h := by
  obtain ⟨ni,nj,hi,hj,hfD,hf⟩ := hf
  obtain ⟨nj',nk,hj',hk,hgD,hg⟩ := hg
  have ej := function_unique hn.1 hj' hj
  subst nj'
  obtain ⟨h',hhD,hh'⟩ := (hm.2.1 f hfD).1 g hgD
  have eh := (hm.2.1 f hfD).2.1 g h h' hgD hh hh'
  subst h'
  exact ⟨ni,nk,hi,hk,hhD,(hm.2.2 ni f g nj h nk (hn.2 i ni hi) hfD hgD hf hh).mp hg⟩

theorem factor_terminal {w D mul e node a i j f t v : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hf : Factor D mul node i j f) (ht : Terminal D mul node a j t) (hv : Product mul f t v) :
    Terminal D mul node a i v := by
  obtain ⟨ni,nj,hi,hj,hfD,hf⟩ := hf
  obtain ⟨nj',hj',htD,ht⟩ := ht
  have ej := function_unique hn.1 hj' hj
  subst nj'
  obtain ⟨v',hvD,hv'⟩ := (hm.2.1 f hfD).1 t htD
  have ev := (hm.2.1 f hfD).2.1 t v v' htD hv hv'
  subst v'
  exact ⟨ni,hi,hvD,(hm.2.2 ni f t nj v a (hn.2 i ni hi) hfD htD hf hv).mp ht⟩

theorem factor_zero {w D mul e zero node i f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hz : PureKuratowski.PairMember M zero e node) (hf : Factor D mul node zero i f) :
    PureKuratowski.PairMember M i f node := by
  obtain ⟨ni,nj,hi,hj,hfD,hf⟩ := hf
  have he := function_unique hn.1 hi hz
  subst ni
  have hjf := ((hm.1.2 f hfD nj).1).mp hf
  exact hjf ▸ hj

theorem terminal_zero {w D mul e zero a node t : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hn : MapsTo w D node)
    (hz : PureKuratowski.PairMember M zero e node) (ht : Terminal D mul node a zero t) : t = a := by
  obtain ⟨ni,hi,htD,ht⟩ := ht
  have he := function_unique hn.1 hi hz
  subst ni
  exact (((hm.1.2 t htD a).1).mp ht).symm

def factor {m : Nat} (D mul node i j f : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ i.succ.succ 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ j.succ.succ 0))
      (.conj (.mem (.bound f.succ.succ) (.bound D.succ.succ))
        (ProjectSyntax.encode id (product mul.succ.succ 1 f.succ.succ 0))))))

theorem factor_freeClosed {m : Nat} (D mul node i j f : Fin m) : (factor D mul node i j f).FreeClosed := by
  simp -implicitDefEqProofs [factor,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem factor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul node i j f : Fin m) :
    Project.Formula.satisfies env (factor D mul node i j f) ↔
      Factor (env.bound D) (env.bound mul) (env.bound node) (env.bound i) (env.bound j) (env.bound f) := by
  simp only [factor,Factor,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,product_semantics (M := M)]
  rfl

def terminal {m : Nat} (D mul node a i t : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ i.succ 0))
    (.conj (.mem (.bound t.succ) (.bound D.succ))
      (ProjectSyntax.encode id (product mul.succ 0 t.succ a.succ))))

theorem terminal_freeClosed {m : Nat} (D mul node a i t : Fin m) : (terminal D mul node a i t).FreeClosed := by
  simp -implicitDefEqProofs [terminal,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem terminal_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul node a i t : Fin m) :
    Project.Formula.satisfies env (terminal D mul node a i t) ↔
      Terminal (env.bound D) (env.bound mul) (env.bound node) (env.bound a) (env.bound i) (env.bound t) := by
  simp only [terminal,Terminal,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,product_semantics (M := M)]
  rfl

def path {m : Nat} (w D mul e zero a node : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo node w D))
    (.conj (.mem (.bound a) (.bound D))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge node zero e))
        (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ))
          (.imp (.mem (.bound 0) (.bound w.succ.succ)) (.imp (natLeF (1 : Fin (m+2)) 0)
            (.existsE (factor D.succ.succ.succ mul.succ.succ.succ node.succ.succ.succ 2 1 0)))))))
          (.forallE (.imp (.mem (.bound 0) (.bound w.succ))
            (.existsE (terminal D.succ.succ mul.succ.succ node.succ.succ a.succ.succ 1 0)))))))

theorem path_freeClosed {m : Nat} (w D mul e zero a node : Fin m) : (path w D mul e zero a node).FreeClosed := by
  simp -implicitDefEqProofs [path,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    natLeF_freeClosed,factor_freeClosed,terminal_freeClosed]

theorem path_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero a node : Fin m) :
    Project.Formula.satisfies env (path w D mul e zero a node) ↔
      Path (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound a) (env.bound node) := by
  simp only [path,Path,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),natLeF_semantics hM,factor_semantics hM,terminal_semantics hM]
  rfl

def OrderedPair (w p : M.Carrier .set) : Prop := ∃ i j,
  (Project.FirstOrderSemantics.reduct M).mem i w ∧ (Project.FirstOrderSemantics.reduct M).mem j w ∧
    NatLe i j ∧ PureKuratowski.Code M p i j

def orderedPair {m : Nat} (w p : Fin m) : Project.Formula 1 m := .existsE (.existsE
  (.conj (.mem (.bound 1) (.bound w.succ.succ)) (.conj (.mem (.bound 0) (.bound w.succ.succ))
    (.conj (natLeF (1 : Fin (m+2)) 0) (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))))))

theorem orderedPair_freeClosed {m : Nat} (w p : Fin m) : (orderedPair w p).FreeClosed := by
  simp -implicitDefEqProofs [orderedPair,Definitional.Formula.FreeClosed,natLeF_freeClosed,PureKuratowskiProject.code]

theorem orderedPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w p : Fin m) :
    Project.Formula.satisfies env (orderedPair w p) ↔ OrderedPair (env.bound w) (env.bound p) := by
  simp only [orderedPair,OrderedPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,natLeF_semantics hM,KuratowskiZF.code_correct hM]
  rfl

def OrderedPairs (w pairs : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p pairs ↔ OrderedPair w p

theorem exists_ordered_pairs (hM : FirstOrder.Theory.Models M nativeZF) (w : M.Carrier .set) :
    ∃ pairs, OrderedPairs w pairs := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨all,ha⟩ := ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) w w
  let schema : Project.UnarySchema 1 := { body := orderedPair 1 0, freeClosed := orderedPair_freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => w, free := fun _ => w }
  obtain ⟨pairs,hp⟩ := ZF.separation_exists_d hZF schema env all
  have he : ∀ p, Project.Formula.satisfies (env.push p) schema.body ↔ OrderedPair w p :=
    fun p => orderedPair_semantics hM (env.push p) 1 0
  refine ⟨pairs,fun p => ⟨fun h => (he p).mp ((hp p).mp h).2,?_⟩⟩
  intro h
  have hcopy := h
  obtain ⟨i,j,hi,hj,_,hc⟩ := hcopy
  exact (hp p).mpr ⟨(ha p).mpr ⟨i,hi,j,hj,hc⟩,(he p).mpr h⟩

def factorPair {m : Nat} (D mul node p f : Fin m) : Project.Formula 1 m := .existsE (.existsE
  (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (factor D.succ.succ mul.succ.succ node.succ.succ 1 0 f.succ.succ)))

theorem factorPair_freeClosed {m : Nat} (D mul node p f : Fin m) : (factorPair D mul node p f).FreeClosed := by
  simp -implicitDefEqProofs [factorPair,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,factor_freeClosed]

theorem factorPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul node p f : Fin m) :
    Project.Formula.satisfies env (factorPair D mul node p f) ↔ ∃ i j,
      PureKuratowski.Code M (env.bound p) i j ∧ Factor (env.bound D) (env.bound mul) (env.bound node) i j (env.bound f) := by
  simp only [factorPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,factor_semantics hM]
  rfl

def FactorTable (w D mul node F : M.Carrier .set) : Prop := ∀ i j f, Product F i j f ↔
  (Project.FirstOrderSemantics.reduct M).mem i w ∧ (Project.FirstOrderSemantics.reduct M).mem j w ∧
    NatLe i j ∧ Factor D mul node i j f

def TerminalTable (w D mul node a T : M.Carrier .set) : Prop := ∀ i t,
  PureKuratowski.PairMember M i t T ↔ (Project.FirstOrderSemantics.reduct M).mem i w ∧ Terminal D mul node a i t

theorem exists_factor_table (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node pairs : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hp : Path w D mul e zero a node) (hPairs : OrderedPairs w pairs) :
    ∃ F, MapsTo pairs D F ∧ FactorTable w D mul node F := by
  let schema : Project.BinarySchema 3 := { body := factorPair 2 3 4 1 0, freeClosed := factorPair_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases D (Fin.cases mul (fun _ => node)), free := fun _ => w }
  have he : ∀ p f, schema.denote env p f ↔ ∃ i j, PureKuratowski.Code M p i j ∧ Factor D mul node i j f :=
    fun p f => factorPair_semantics hM ((env.push p).push f) 2 3 4 1 0
  obtain ⟨F,hF,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := pairs) (target := D) (by
      intro p hpi
      obtain ⟨i,j,hi,hj,hij,hcode⟩ := (hPairs p).mp hpi
      obtain ⟨f,hf⟩ := hp.2.2.2.1 i j hi hj hij
      exact ⟨f,(he p f).mpr ⟨i,j,hcode,hf⟩⟩) (by
      intro p _ f g hf hg
      obtain ⟨i,j,hcode,hf⟩ := (he p f).mp hf
      obtain ⟨i',j',hcode',hg⟩ := (he p g).mp hg
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact factor_unique hm hp.1 hf hg) (by
      intro p f _ hf
      obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (he p f).mp hf
      exact hfD)
  refine ⟨F,(ForcingSupportSize.native_mapsTo hM pairs D F).mpr hF,fun i j f => ?_⟩
  constructor
  · rintro ⟨p,hcode,hpf⟩
    obtain ⟨hpi,hvf⟩ := (hgraph p f).mp hpf
    obtain ⟨i',j',hi,hj,hij,hcode'⟩ := (hPairs p).mp hpi
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    obtain ⟨i'',j'',hcode'',hf⟩ := (he p f).mp hvf
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode''
    exact ⟨hi,hj,hij,hf⟩
  · rintro ⟨hi,hj,hij,hf⟩
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM i j
    exact ⟨p,hcode,(hgraph p f).mpr ⟨(hPairs p).mpr ⟨i,j,hi,hj,hij,hcode⟩,(he p f).mpr ⟨i,j,hcode,hf⟩⟩⟩

theorem exists_terminal_table (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hp : Path w D mul e zero a node) : ∃ T, MapsTo w D T ∧ TerminalTable w D mul node a T := by
  let schema : Project.BinarySchema 4 := { body := terminal 2 3 4 5 1 0, freeClosed := terminal_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := Fin.cases D (Fin.cases mul (Fin.cases node (fun _ => a))), free := fun _ => w }
  have he : ∀ i t, schema.denote env i t ↔ Terminal D mul node a i t :=
    fun i t => terminal_semantics hM ((env.push i).push t) 2 3 4 5 1 0
  obtain ⟨T,hT,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := w) (target := D) (by
      intro i hi
      obtain ⟨t,ht⟩ := hp.2.2.2.2 i hi
      exact ⟨t,(he i t).mpr ht⟩) (by
      intro i _ t v ht hv
      exact terminal_unique hm hp.1 ((he i t).mp ht) ((he i v).mp hv)) (by
      intro i t _ ht
      exact ((he i t).mp ht).choose_spec.2.1)
  exact ⟨T,(ForcingSupportSize.native_mapsTo hM w D T).mpr hT,fun i t => (hgraph i t).trans (and_congr_right fun _ => he i t)⟩

def TableLaws (w mul e zero a node F T : M.Carrier .set) : Prop :=
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i w → Product F i i e) ∧
  (∀ i n, (Project.FirstOrderSemantics.reduct M).mem i w → PureKuratowski.PairMember M i n node → Product F zero i n) ∧
  (∀ i j k f g h, Product F i j f → Product F j k g → Product mul f g h → Product F i k h) ∧
  PureKuratowski.PairMember M zero a T ∧
  (∀ i j f t v, Product F i j f → PureKuratowski.PairMember M j t T → Product mul f t v → PureKuratowski.PairMember M i v T)

theorem table_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F) (hT : TerminalTable w D mul node a T) : TableLaws w mul e zero a node F T := by
  have hzw := function_input hp.1.1 hp.2.2.1
  refine ⟨fun i hi => (hF i i e).mpr ⟨hi,hi,Or.inl rfl,factor_self hm hp.1 hi⟩,?_,?_,?_,?_⟩
  · intro i n hi hin
    have hzi : NatLe zero i := by
      rcases nat_compare hM hw hzw hi with he | hzi | hiz
      · exact Or.inl he
      · exact Or.inr hzi
      · exact (hz i hiz).elim
    exact (hF zero i n).mpr ⟨hzw,hi,hzi,e,n,hp.2.2.1,hin,hp.1.2 i n hin,
      ((hm.1.2 n (hp.1.2 i n hin) n).1).mpr rfl⟩
  · intro i j k f g h hij hjk hfg
    obtain ⟨hi,hj,hij,hf⟩ := (hF i j f).mp hij
    obtain ⟨_,hk,hjk,hg⟩ := (hF j k g).mp hjk
    have hik : NatLe i k := by
      rcases hij with he | hij
      · exact he.symm ▸ hjk
      · rcases hjk with he | hjk
        · exact Or.inr (he ▸ hij)
        · exact Or.inr ((hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) k hk).transitive j hjk i hij)
    exact (hF i k h).mpr ⟨hi,hk,hik,factor_trans hm hp.1 hf hg hfg⟩
  · exact (hT zero a).mpr ⟨hzw,e,hp.2.2.1,hp.2.1,((hm.1.2 a hp.2.1 a).1).mpr rfl⟩
  · intro i j f t v hf ht hft
    obtain ⟨hi,_,_,hf⟩ := (hF i j f).mp hf
    obtain ⟨_,ht⟩ := (hT j t).mp ht
    exact (hT i v).mpr ⟨hi,factor_terminal hm hp.1 hf ht hft⟩

def orderedPairs {m : Nat} (w pairs : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound pairs.succ)) (orderedPair w.succ 0))

theorem orderedPairs_freeClosed {m : Nat} (w pairs : Fin m) : (orderedPairs w pairs).FreeClosed := by
  simp -implicitDefEqProofs [orderedPairs,Definitional.Formula.FreeClosed,orderedPair_freeClosed]

theorem orderedPairs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w pairs : Fin m) :
    Project.Formula.satisfies env (orderedPairs w pairs) ↔ OrderedPairs (env.bound w) (env.bound pairs) := by
  simp only [orderedPairs,OrderedPairs,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,orderedPair_semantics hM]
  rfl

def factorTable {m : Nat} (w D mul node F : Fin m) : Project.Formula 1 m := .forallE (.forallE (.forallE
  (.iff (ProjectSyntax.encode id (product F.succ.succ.succ 2 1 0))
    (.conj (.mem (.bound 2) (.bound w.succ.succ.succ)) (.conj (.mem (.bound 1) (.bound w.succ.succ.succ))
      (.conj (natLeF (2 : Fin (m+3)) 1) (factor D.succ.succ.succ mul.succ.succ.succ node.succ.succ.succ 2 1 0)))))))

theorem factorTable_freeClosed {m : Nat} (w D mul node F : Fin m) : (factorTable w D mul node F).FreeClosed := by
  simp -implicitDefEqProofs [factorTable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,natLeF_freeClosed,factor_freeClosed]

theorem factorTable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul node F : Fin m) :
    Project.Formula.satisfies env (factorTable w D mul node F) ↔
      FactorTable (env.bound w) (env.bound D) (env.bound mul) (env.bound node) (env.bound F) := by
  simp only [factorTable,FactorTable,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),natLeF_semantics hM,factor_semantics hM]
  rfl

def terminalTable {m : Nat} (w D mul node a T : Fin m) : Project.Formula 1 m := .forallE (.forallE
  (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge T.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound w.succ.succ)) (terminal D.succ.succ mul.succ.succ node.succ.succ a.succ.succ 1 0))))

theorem terminalTable_freeClosed {m : Nat} (w D mul node a T : Fin m) : (terminalTable w D mul node a T).FreeClosed := by
  simp -implicitDefEqProofs [terminalTable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,terminal_freeClosed]

theorem terminalTable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul node a T : Fin m) :
    Project.Formula.satisfies env (terminalTable w D mul node a T) ↔
      TerminalTable (env.bound w) (env.bound D) (env.bound mul) (env.bound node) (env.bound a) (env.bound T) := by
  simp only [terminalTable,TerminalTable,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,terminal_semantics hM]
  rfl

def tableLaws {m : Nat} (w mul e zero a node F T : Fin m) : Project.Formula 1 m :=
  let up5 : Fin m → Fin (m+5) := fun i => i.succ.succ.succ.succ.succ
  let up6 : Fin m → Fin (m+6) := fun i => i.succ.succ.succ.succ.succ.succ
  .conj (.forallE (.imp (.mem (.bound 0) (.bound w.succ)) (ProjectSyntax.encode id (product F.succ 0 0 e.succ))))
    (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ 1 0))
        (ProjectSyntax.encode id (product F.succ.succ zero.succ.succ 1 0))))))
      (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
        (.imp (ProjectSyntax.encode id (product (up6 F) 5 4 2))
          (.imp (ProjectSyntax.encode id (product (up6 F) 4 3 1))
            (.imp (ProjectSyntax.encode id (product (up6 mul) 2 1 0))
              (ProjectSyntax.encode id (product (up6 F) 5 3 0)))))))))))
        (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge T zero a))
          (.forallE (.forallE (.forallE (.forallE (.forallE
            (.imp (ProjectSyntax.encode id (product (up5 F) 4 3 2))
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up5 T) 3 1))
                (.imp (ProjectSyntax.encode id (product (up5 mul) 2 1 0))
                  (ProjectSyntax.encode id (Source.SetLanguage.edge (up5 T) 4 0)))))))))))))

theorem tableLaws_freeClosed {m : Nat} (w mul e zero a node F T : Fin m) : (tableLaws w mul e zero a node F T).FreeClosed := by
  simp -implicitDefEqProofs [tableLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem tableLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul e zero a node F T : Fin m) :
    Project.Formula.satisfies env (tableLaws w mul e zero a node F T) ↔
      TableLaws (env.bound w) (env.bound mul) (env.bound e) (env.bound zero) (env.bound a) (env.bound node) (env.bound F) (env.bound T) := by
  simp only [tableLaws,TableLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,product_semantics (M := M)]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (.forallE (.neg (.mem (.bound 0) (.bound 5))))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 7) 2 3))
        (.imp (path (0 : Fin 7) 1 2 3 4 5 6)
          (.existsE (.existsE (.existsE (.conj (orderedPairs (3 : Fin 10) 2)
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 10) 2 4))
              (.conj (factorTable (3 : Fin 10) 4 5 9 1)
                (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 10) 3 4))
                  (.conj (terminalTable (3 : Fin 10) 4 5 9 8 0)
                    (tableLaws (3 : Fin 10) 5 6 7 8 9 1 0)))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    path_freeClosed,orderedPairs_freeClosed,factorTable_freeClosed,terminalTable_freeClosed,tableLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),path_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,orderedPairs_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),factorTable_semantics hM,terminalTable_semantics hM,tableLaws_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM (bound 0)
  obtain ⟨F,hFm,hF⟩ := exists_factor_table hM hm hp hpairs
  obtain ⟨T,hTm,hT⟩ := exists_terminal_table hM hm hp
  exact ⟨pairs,F,T,hpairs,hFm,hF,hTm,hT,table_laws hM hw hz hm hp hF hT⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbePath
