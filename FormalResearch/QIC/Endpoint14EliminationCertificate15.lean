module

public import FormalResearch.QIC.Endpoint14EliminationCertificateBase
meta import FormalResearch.QIC.Endpoint14EliminationCertificateBase


@[expose] public section

namespace FormalResearch.QIC

lemma endpointElim_certificate_15 :
    endpointElimCertificateAt (15 : EndpointSampleIndex) := by
  native_decide

end FormalResearch.QIC
