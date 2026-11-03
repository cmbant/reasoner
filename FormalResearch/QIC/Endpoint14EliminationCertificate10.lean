module

public import FormalResearch.QIC.Endpoint14EliminationCertificateBase
meta import FormalResearch.QIC.Endpoint14EliminationCertificateBase


@[expose] public section

namespace FormalResearch.QIC

lemma endpointElim_certificate_10 :
    endpointElimCertificateAt (10 : EndpointSampleIndex) := by
  native_decide

end FormalResearch.QIC
