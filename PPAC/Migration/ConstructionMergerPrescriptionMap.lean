/- Pinned ConservativeExtensions.OverlapPrescription.map/rel_map_iff/
valid_map_iff:121-255, consumed by MonoidRounds.MergerData.map:31.
Actual one-step start graph, never a transitive closure. -/
import PPAC.Migration.ConstructionMergerRelations
import PPAC.Migration.ConstructionProbeSharedIntersections

namespace PPAC.Migration.ConstructionMergerPrescriptionMap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerRelations
open ConstructionProbeConservative (Conservative)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Entry (P f q : M.Carrier .set) : Prop :=
  ∃ i j a b fa fb ij ab, PureKuratowski.Code M ij i j ∧ PureKuratowski.Code M ab fa fb ∧
    PureKuratowski.Code M q ij ab ∧ Start P i j a b ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f

def Graph (P f PN : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q PN ↔ Entry P f q

def Mapped (P f PN : M.Carrier .set) : Prop := ∀ i j fa fb,
  Start PN i j fa fb ↔ ∃ a b, Start P i j a b ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f

def entry {m : Nat} (P f q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (PureKuratowskiProject.code (.bound (1 : Fin (m+8))) (.bound (7 : Fin (m+8))) (.bound (6 : Fin (m+8))))
  (.conj (PureKuratowskiProject.code (.bound (0 : Fin (m+8))) (.bound (3 : Fin (m+8))) (.bound (2 : Fin
  (m+8)))) (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ.succ.succ.succ.succ) (.bound (1
  : Fin (m+8))) (.bound (0 : Fin (m+8)))) (.conj (ConstructionMergerRelations.start
  P.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin (m+8)))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+8)) (3 : Fin (m+8)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+8)) (2 : Fin (m+8)))))))))))))))))

theorem entry_freeClosed {m : Nat} (P f q : Fin m) :
    (entry P f q).FreeClosed := by
  simp -implicitDefEqProofs [entry,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code,ConstructionMergerRelations.start_freeClosed]

theorem entry_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P f q : Fin m) :
    Project.Formula.satisfies env (entry P f q) ↔ Entry (env.bound P) (env.bound f) (env.bound q) := by
  simp only [entry,Entry,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,ConstructionMergerRelations.start_semantics hM]
  rfl


theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {n D P f N : M.Carrier .set} (hP : Prescription n D P) (hf : MapsTo D N f) :
    ∃ PN, Graph P f PN := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨A,hA⟩ := ZF.exists_cartesianProduct hZF I n n
  obtain ⟨B,hB⟩ := ZF.exists_cartesianProduct hZF I N N
  obtain ⟨Box,hBox⟩ := ZF.exists_cartesianProduct hZF I A B
  let schema : Project.UnarySchema 2 := { body := entry 1 2 0, freeClosed := entry_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases P (fun _ => f), free := fun _ => P }
  have he (q) : schema.denote env q ↔ Entry P f q := entry_semantics hM (env.push q) 1 2 0
  obtain ⟨PN,hPN⟩ := ZF.separation_exists_d hZF schema env Box
  refine ⟨PN,fun q => ?_⟩
  constructor
  · exact fun h => (he q).mp ((hPN q).mp h).2
  · intro h
    refine (hPN q).mpr ⟨?_,(he q).mpr h⟩
    obtain ⟨i,j,a,b,fa,fb,ij,ab,hij,hab,hq,hS,hafa,hbfb⟩ := h
    have hRange := hP.1 i j a b hS
    exact (hBox q).mpr ⟨ij,(hA ij).mpr ⟨i,hRange.1,j,hRange.2.1,hij⟩,
      ab,(hB ab).mpr ⟨fa,hf.2 a fa hafa,fb,hf.2 b fb hbfb,hab⟩,hq⟩

theorem mapped (hM : FirstOrder.Theory.Models M nativeZF)
    {P f PN : M.Carrier .set} (hG : Graph P f PN) : Mapped P f PN := by
  intro i j fa fb
  constructor
  · rintro ⟨ab,hab,ij,hij,q,hq,hmem⟩
    obtain ⟨i',j',a,b,fa',fb',ij',ab',hij',hab',hq',hS,hafa,hbfb⟩ := (hG q).mp hmem
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hij hij'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hab hab'
    exact ⟨a,b,hS,hafa,hbfb⟩
  · rintro ⟨a,b,hS,hafa,hbfb⟩
    obtain ⟨ij,hij⟩ := KuratowskiZF.exists_code hM i j
    obtain ⟨ab,hab⟩ := KuratowskiZF.exists_code hM fa fb
    obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM ij ab
    exact ⟨ab,hab,ij,hij,q,hq,(hG q).mpr ⟨i,j,a,b,fa,fb,ij,ab,hij,hab,hq,hS,hafa,hbfb⟩⟩

theorem prescription {n D P f N PN : M.Carrier .set}
    (hP : Prescription n D P) (hf : MapsTo D N f) (hMap : Mapped P f PN) : Prescription n N PN := by
  constructor
  · intro i j fa fb hS
    obtain ⟨a,b,hab,hafa,hbfb⟩ := (hMap i j fa fb).mp hS
    have hRange := hP.1 i j a b hab
    exact ⟨hRange.1,hRange.2.1,hf.2 a fa hafa,hf.2 b fb hbfb⟩
  · intro i j fa fb fc fd h1 h2
    obtain ⟨a,b,hab,hafa,hbfb⟩ := (hMap i j fa fb).mp h1
    obtain ⟨c,d,hcd,hcfc,hdfd⟩ := (hMap i j fc fd).mp h2
    obtain ⟨rfl,rfl⟩ := hP.2 i j a b c d hab hcd
    exact ⟨function_unique hf.1 hafa hcfc,function_unique hf.1 hbfb hdfd⟩


theorem rel_map {n D mul P f N mulN PN i j x y fx fy : M.Carrier .set}
    (hP : Prescription n D P) (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hMap : Mapped P f PN) (h : CopyRel n D mul P i x j y)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f) :
    CopyRel n N mulN PN i fx j fy := by
  obtain ⟨hi,hx,hj,hy,h⟩ := h
  refine ⟨hi,hf.2 x fx hfx,hj,hf.2 y fy hfy,?_⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨hne,a,b,t,hS,ht,hat,hbt⟩
  · exact Or.inl ⟨rfl,function_unique hf.1 hfx hfy⟩
  · have hRange := hP.1 i j a b hS
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a hRange.2.2.1
    obtain ⟨fb,hfb,_⟩ := hf.1.2 b hRange.2.2.2
    obtain ⟨ft,hft,_⟩ := hf.1.2 t ht
    exact Or.inr ⟨hne,fa,fb,ft,(hMap i j fa fb).mpr ⟨a,b,hS,hfa,hfb⟩,hf.2 t ft hft,
      hPres a t x fa ft fx hat hfa hft hfx,hPres b t y fb ft fy hbt hfb hft hfy⟩

theorem rel_map_iff {n D mul e P f N mulN eN PN i j x y fx fy : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hCons : Conservative D N mul mulN f)
    (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f) :
    CopyRel n N mulN PN i fx j fy ↔ CopyRel n D mul P i x j y := by
  constructor
  · rintro ⟨hi,_,hj,_,h⟩
    refine ⟨hi,function_input hCons.1.1.1 hfx,hj,function_input hCons.1.1.1 hfy,?_⟩
    rcases h with ⟨rfl,heq⟩ | ⟨hne,fa,fb,t,hStart,ht,hat,hbt⟩
    · exact Or.inl ⟨rfl,hCons.1.2 x y fx hfx (heq.symm ▸ hfy)⟩
    · obtain ⟨a,b,hS,hfa,hfb⟩ := (hMap i j fa fb).mp hStart
      obtain ⟨u,hu,hax⟩ := ConstructionProbeAlphabetMap.factor_eq hm hmN hCons.1 hPres hCons.2.1 hfa hfx ht hat
      obtain ⟨v,hv,hby⟩ := ConstructionProbeAlphabetMap.factor_eq hm hmN hCons.1 hPres hCons.2.1 hfb hfy ht hbt
      have huv := hCons.1.2 u v t hu hv
      subst v
      exact Or.inr ⟨hne,a,b,u,hS,function_input hCons.1.1.1 hu,hax,hby⟩
  · exact fun h => rel_map hP hCons.1.1 hPres hMap h hfx hfy

theorem rel_start {n D mul e P i j a b : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hne : i ≠ j) (hS : Start P i j a b) : CopyRel n D mul P i a j b := by
  have h := hP.1 i j a b hS
  exact ⟨h.1,h.2.2.1,h.2.1,h.2.2.2,Or.inr ⟨hne,a,b,e,hS,hm.1.1,
    (hm.1.2 a h.2.2.1 a).2.mpr rfl,(hm.1.2 b h.2.2.2 b).2.mpr rfl⟩⟩

theorem valid_of_map {n D mul e P f N mulN eN PN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hCons : Conservative D N mul mulN f)
    (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hValid : Valid n N mulN PN) : Valid n D mul P := by
  refine ⟨?_,?_,?_⟩
  · intro i x hi hx
    obtain ⟨fx,hfx,_⟩ := hCons.1.1.1.2 x hx
    exact (rel_map_iff hm hmN hP hCons hPres hMap hfx hfx).mp (hValid.1 i fx hi (hCons.1.1.2 x fx hfx))
  · intro i x j y h
    obtain ⟨fx,hfx,_⟩ := hCons.1.1.1.2 x h.2.1
    obtain ⟨fy,hfy,_⟩ := hCons.1.1.1.2 y h.2.2.2.1
    exact (rel_map_iff hm hmN hP hCons hPres hMap hfy hfx).mp (hValid.2.1 i fx j fy (rel_map hP hCons.1.1 hPres hMap h hfx hfy))
  · intro i x j y k z hxy hyz
    obtain ⟨fx,hfx,_⟩ := hCons.1.1.1.2 x hxy.2.1
    obtain ⟨fy,hfy,_⟩ := hCons.1.1.1.2 y hxy.2.2.2.1
    obtain ⟨fz,hfz,_⟩ := hCons.1.1.1.2 z hyz.2.2.2.1
    exact (rel_map_iff hm hmN hP hCons hPres hMap hfx hfz).mp (hValid.2.2 i fx j fy k fz
      (rel_map hP hCons.1.1 hPres hMap hxy hfx hfy) (rel_map hP hCons.1.1 hPres hMap hyz hfy hfz))

/-- Literal source starts_of_rel_map; target elements need not lie in the image. -/
theorem starts_of_rel_map {n N mulN P f PN i j x y : M.Carrier .set}
    (hMap : Mapped P f PN) (hne : i ≠ j) (h : CopyRel n N mulN PN i x j y) :
    ∃ a b fa fb t, Start P i j a b ∧ PureKuratowski.PairMember M a fa f ∧
      PureKuratowski.PairMember M b fb f ∧ (Project.FirstOrderSemantics.reduct M).mem t N ∧
      Product mulN fa t x ∧ Product mulN fb t y := by
  rcases h.2.2.2.2 with ⟨heq,_⟩ | ⟨_,fa,fb,t,hS,ht,hx,hy⟩
  · exact (hne heq).elim
  · obtain ⟨a,b,hS,hfa,hfb⟩ := (hMap i j fa fb).mp hS
    exact ⟨a,b,fa,fb,t,hS,hfa,hfb,ht,hx,hy⟩

/-- Source valid_map's old-middle-join proof, against ALL new elements.
No closure of the one-step relation and no supplied target validity. -/
theorem valid_map {n D mul e P f N mulN eN PN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hCons : Conservative D N mul mulN f)
    (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hJoins : ConditionalJoins D mul) (hValid : Valid n D mul P) : Valid n N mulN PN := by
  have hf := hCons.1.1
  have hPN := prescription hP hf hMap
  refine ⟨?_,?_,?_⟩
  · intro i x hi hx
    exact ⟨hi,hx,hi,hx,Or.inl ⟨rfl,rfl⟩⟩
  · intro i x j y hxy
    rcases hxy.2.2.2.2 with ⟨hij,hxy'⟩ | ⟨hne,fa,fb,t,hS,ht,hat,hbt⟩
    · exact ⟨hxy.2.2.1,hxy.2.2.2.1,hxy.1,hxy.2.1,Or.inl ⟨hij.symm,hxy'.symm⟩⟩
    · obtain ⟨a,b,hS,hfa,hfb⟩ := (hMap i j fa fb).mp hS
      exact rel_mul hmN hPN ht (rel_map hP hf hPres hMap
        (hValid.2.1 i a j b (rel_start hm hP hne hS)) hfb hfa) hbt hat
  · intro i x j y k z hxy hyz
    by_cases hij : i = j
    · subst j
      have h := (rel_same_copy hxy.1 hxy.2.1 hxy.2.2.2.1).mp hxy
      subst y
      exact hyz
    by_cases hjk : j = k
    · subst k
      have h := (rel_same_copy hyz.1 hyz.2.1 hyz.2.2.2.1).mp hyz
      subst z
      exact hxy
    obtain ⟨a,b,fa,fb,s,hSab,hfa,hfb,hs,hax,hby⟩ := starts_of_rel_map hMap hij hxy
    obtain ⟨c,d,fc,fd,t,hScd,hfc,hfd,ht,hcy,hdz⟩ := starts_of_rel_map hMap hjk hyz
    have hb := function_input hf.1 hfb
    have hc := function_input hf.1 hfc
    obtain ⟨q,hq,hbq,hcq⟩ := hCons.2.2.2 b c fb fc hfb hfc
      ⟨y,hxy.2.2.2.1,⟨s,hs,hby⟩,⟨t,ht,hcy⟩⟩
    obtain ⟨j0,hj0,hJoin⟩ := hJoins b c q hb hc hq hbq hcq
    have hSelf : Divides D mul j0 j0 := ⟨e,hm.1.1,(hm.1.2 j0 hj0 j0).2.mpr rfl⟩
    obtain ⟨⟨r,hr,hbr⟩,⟨u,hu,hcu⟩⟩ := (hJoin j0 hj0).mpr hSelf
    obtain ⟨fj0,hfj0,_⟩ := hf.1.2 j0 hj0
    obtain ⟨fr,hfr,_⟩ := hf.1.2 r hr
    obtain ⟨fu,hfu,_⟩ := hf.1.2 u hu
    obtain ⟨v,hv,hjv⟩ := (hCons.2.2.1 b c j0 fb fc fj0 hfb hfc hfj0 hJoin y hxy.2.2.2.1).mp
      ⟨⟨s,hs,hby⟩,⟨t,ht,hcy⟩⟩
    have hfrN := hf.2 r fr hfr
    have hfuN := hf.2 u fu hfu
    obtain ⟨rv,hrv,hfrv⟩ := (hmN.2.1 fr hfrN).1 v hv
    obtain ⟨uv,huv,hfuv⟩ := (hmN.2.1 fu hfuN).1 v hv
    have hfbfr := hPres b r j0 fb fr fj0 hbr hfb hfr hfj0
    have hfcfu := hPres c u j0 fc fu fj0 hcu hfc hfu hfj0
    have hfbN := hf.2 b fb hfb
    have hfcN := hf.2 c fc hfc
    have hsrv := (hmN.2.1 fb hfbN).2.2 s rv y hs hrv hby
      ((hmN.2.2 fb fr v fj0 rv y hfbN hfrN hv hfbfr hfrv).mp hjv)
    have htuv := (hmN.2.1 fc hfcN).2.2 t uv y ht huv hcy
      ((hmN.2.2 fc fu v fj0 uv y hfcN hfuN hv hfcfu hfuv).mp hjv)
    have ha := function_input hf.1 hfa
    have hd := function_input hf.1 hfd
    obtain ⟨ar,harD,har⟩ := (hm.2.1 a ha).1 r hr
    obtain ⟨du,hduD,hdu⟩ := (hm.2.1 d hd).1 u hu
    obtain ⟨far,hfar,_⟩ := hf.1.2 ar harD
    obtain ⟨fdu,hfdu,_⟩ := hf.1.2 du hduD
    have h1 := rel_mul hm hP hr (rel_start hm hP hij hSab) har hbr
    have h2 := rel_mul hm hP hu (rel_start hm hP hjk hScd) hcu hdu
    have h3 := rel_map hP hf hPres hMap (hValid.2.2 i ar j j0 k du h1 h2) hfar hfdu
    have hfarv : Product mulN far v x := (hmN.2.2 fa fr v far rv x (hf.2 a fa hfa) hfrN hv
      (hPres a r ar fa fr far har hfa hfr hfar) hfrv).mpr (hsrv ▸ hax)
    have hfduv : Product mulN fdu v z := (hmN.2.2 fd fu v fdu uv z (hf.2 d fd hfd) hfuN hv
      (hPres d u du fd fu fdu hdu hfd hfu hfdu) hfuv).mpr (htuv ▸ hdz)
    exact rel_mul hmN hPN hv h3 hfarv hfduv

theorem valid_map_iff {n D mul e P f N mulN eN PN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hCons : Conservative D N mul mulN f)
    (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hJoins : ConditionalJoins D mul) : Valid n N mulN PN ↔ Valid n D mul P :=
  ⟨valid_of_map hm hmN hP hCons hPres hMap,valid_map hm hmN hP hCons hPres hMap hJoins⟩

theorem graph_unique (hM : FirstOrder.Theory.Models M nativeZF) {P f A B : M.Carrier .set}
    (hA : Graph P f A) (hB : Graph P f B) : A = B :=
  (ModelTransfer.extensionality hM).eq_of_same_members A B (fun q => (hA q).trans (hB q).symm)

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P f N mulN eN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hP : Prescription n D P) (hCons : Conservative D N mul mulN f)
    (hPres : PreservesProducts mul mulN f) (hJoins : ConditionalJoins D mul) :
    ∃ PN, Graph P f PN ∧ Mapped P f PN ∧ Prescription n N PN ∧
      (Valid n N mulN PN ↔ Valid n D mul P) ∧
      (∀ i j x y fx fy, PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
        (CopyRel n N mulN PN i fx j fy ↔ CopyRel n D mul P i x j y)) ∧
      ∀ other, Graph P f other → other = PN := by
  obtain ⟨PN,hG⟩ := exists_graph hM hP hCons.1.1
  have hMap := mapped hM hG
  exact ⟨PN,hG,hMap,prescription hP hCons.1.1 hMap,valid_map_iff hm hmN hP hCons hPres hMap hJoins,
    fun _ _ _ _ _ _ hx hy => rel_map_iff hm hmN hP hCons hPres hMap hx hy,
    fun _ hOther => graph_unique hM hOther hG⟩

end PPAC.Migration.ConstructionMergerPrescriptionMap
