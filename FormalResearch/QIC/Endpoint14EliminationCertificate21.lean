module

public import FormalResearch.QIC.Endpoint14EliminationCertificateBase


@[expose] public section

namespace FormalResearch.QIC

lemma endpointElim_certificate21_single :
    endpointElimCertificateAt (21 : EndpointSampleIndex) := by
  native_decide

end FormalResearch.QIC
