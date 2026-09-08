import ComplementedSubspace.ComplexProjectionRealEquiv
import ComplementedSubspace.ComplexCorollaryAssembly

/-! The complex unconditional-basis theorem, using the actual finite complex
projection and a whole-space real equivalence to the verified real frame sum.
The continuous dual is handled by the real/complex dual isometry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

/-- For every positive tolerance there is a projection on a complex Banach
space with an actual 1-unconditional basis, of norm below one plus that
tolerance, whose range and continuous dual have no unconditional basis. -/
theorem complexCorollary : ComplexCorollaryStatement := by
  exact complexCorollary_of_recursive_range_equivalences
    (fun s => ⟨s.predecessorComplexRangeRealEquiv⟩)

end ComplementedSubspace
