module

public import FormalResearch.QIC.Endpoint14EliminationCertificateBase


@[expose] public section

namespace FormalResearch.QIC

lemma endpointElim_certificate_11 :
    endpointElimCertificateAt (11 : EndpointSampleIndex) := by
  native_decide

end FormalResearch.QIC
