module
import JacobiKernelHarness
set_option maxHeartbeats 0
set_option maxRecDepth 4096
example {R : Type*} [Ring R] (a b c : R) :
    a * (b * c - c * b) - (b * c - c * b) * a +
    b * (c * a - a * c) - (c * a - a * c) * b +
    c * (a * b - b * a) - (a * b - b * a) * c = 0 := by
  jacobi_kernel_paired
