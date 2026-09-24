import RelationalPerimeter

/-!
# Public-root import gate

This module is a downstream-style build check.  Its presence in the default
Lake target ensures that the public `RelationalPerimeter` module is registered,
built, and importable rather than merely valid when elaborated as a source file.
-/

namespace RelationalPerimeter.Tests.PublicRootImport

def publicEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence

def publicFamily :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family

end RelationalPerimeter.Tests.PublicRootImport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicFamily
/- AXIOM_AUDIT_END -/
