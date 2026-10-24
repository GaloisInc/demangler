{ mkDerivation, base, containers, directory, hspec, lens, lib
, prettyprinter, process, sayable, tasty, tasty-hspec
, template-haskell, text, transformers
}:
mkDerivation {
  pname = "demangler";
  version = "1.3.2.0";
  src = ./..;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers lens sayable template-haskell text
  ];
  executableHaskellDepends = [ base sayable text transformers ];
  testHaskellDepends = [
    base directory hspec prettyprinter process sayable tasty
    tasty-hspec text transformers
  ];
  description = "Demangler for C++ mangled names";
  license = lib.licenses.bsd3;
  mainProgram = "demangle";
}
