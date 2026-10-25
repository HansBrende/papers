import LeanMachine.HomogeneousInflation

/-! The paper uses the shared construction directly. Its space `W` is the
product of the type spaces, with each typed coefficient extended by zero. -/

namespace CoverStorage

export LeanMachine.HomogeneousInflation
  (sheetCheck inflatedCheck sheetReindex reindex_inflated kernelEquiv
    finrank_kernel_inflated rate_cross_product)

end CoverStorage
