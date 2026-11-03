module

public import FormalResearch.QIC.Endpoint14EliminationCertificateBase


@[expose] public section

namespace FormalResearch.QIC

lemma endpointElim_certificate_14 :
    endpointElimCertificateAt (14 : EndpointSampleIndex) := by
  native_decide

end FormalResearch.QIC
