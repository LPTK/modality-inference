import ModalityInference.ComparisonAmbientDriver
import ModalityInference.ComparisonAmbientNormalization

/-! Ambient comparison after conservative raw-edge normalization. Every original
input name is retained, so fresh source/target namespaces stay unchanged. -/
namespace ModalityInference.ComparisonNormalizedAmbientDriver

def run (fuel : Nat) (ambient : Bounds) (source target : Scheme) : RunResult CompareSubstitution :=
  ComparisonAmbientDriver.run fuel (ComparisonAmbientNormalization.normalize ambient) source target

end ModalityInference.ComparisonNormalizedAmbientDriver
