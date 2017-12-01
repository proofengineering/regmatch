set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add proofengineering-dev http://opam-dev.proofengineering.org

opam pin add coq ${COQ_VERSION} --yes --verbose

case ${MODE} in
  matcher)
    opam pin add matcher . --yes --verbose
    ;;
  *)
    opam pin add regexp . --yes --verbose
    ;;
esac
