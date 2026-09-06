import ComplementedSubspace.LatticeApproximation
import ComplementedSubspace.DPRIsomorphism
import ComplementedSubspace.CorollaryStatement

/-!
# The universal nonlattice deduction from dual DPR obstructions

The bidual obstruction is an explicit hypothesis here, to be supplied by the
construction. No reflexivity or general local-reflexivity theorem is assumed.
-/

noncomputable section

namespace ComplementedSubspace

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem not_isomorphic_to_realBanachLattice_of_dual_DPR_top
    (hZ : chiDPR (StrongDual ℝ Z) = ⊤) :
    ¬ IsIsomorphicToRealBanachLattice Z := by
  rintro ⟨L, hL, ⟨e⟩⟩
  obtain ⟨latticeOrder, horder, hscalar, hsolid⟩ := hL
  letI : Lattice L.Carrier := latticeOrder
  letI : IsOrderedAddMonoid L.Carrier := horder
  letI : PosSMulMono ℝ L.Carrier := hscalar
  letI : HasSolidNorm L.Carrier := hsolid
  letI : VectorLattice L.Carrier := {}
  letI : NormedVectorLattice L.Carrier := {}
  letI : BanachLattice L.Carrier := {}
  have hLD : HasDPRLocalUnconditionalStructure (StrongDual ℝ L.Carrier) :=
    hasDPRLocalUnconditionalStructure_dual_lattice
  let eD : StrongDual ℝ Z ≃L[ℝ] StrongDual ℝ L.Carrier :=
    e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hZD := hLD.of_continuousLinearEquiv eD.symm
  change chiDPR (StrongDual ℝ Z) < ⊤ at hZD
  rw [hZ] at hZD
  exact (lt_irrefl _) hZD

theorem not_isomorphic_to_realBanachLattice_primal_and_dual
    (hdual : chiDPR (StrongDual ℝ Z) = ⊤)
    (hbidual : chiDPR (StrongDual ℝ (StrongDual ℝ Z)) = ⊤) :
    ¬ IsIsomorphicToRealBanachLattice Z ∧
      ¬ IsIsomorphicToRealBanachLattice (StrongDual ℝ Z) :=
  ⟨not_isomorphic_to_realBanachLattice_of_dual_DPR_top hdual,
    not_isomorphic_to_realBanachLattice_of_dual_DPR_top hbidual⟩

end ComplementedSubspace
