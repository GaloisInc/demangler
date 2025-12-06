{
  description = "Haskell C++ name demangler";

  nixConfig.bash-prompt-suffix = "demangler.env} ";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    levers = {
      url = "github:kquick/nix-levers";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    sayable = {
      url = "github:kquick/sayable";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.levers.follows = "levers";
    };
  };

  outputs = { self, nixpkgs, levers, sayable }:
    rec
      {
        apps = levers.eachSystem (s:
          rec
          {
            demangle = {
              type = "app";
              program = "${self.packages.${s}.demangler}/bin/demangle";
            };
            default = demangle;
          });

        devShells = levers.haskellShells
          { inherit nixpkgs;
            flake = self;
            defaultPkg = "demangler";
            # additionalPackages = pkgs: [ pkgs.? ];
          };

        packages = levers.eachSystem (system:  # KWQ: add taphRep
          let mkHaskell = levers.mkHaskellPkg { inherit nixpkgs system; };
              pkgs = import nixpkgs { inherit system; };
          in rec
            {
              default = demangler;
              demangler = mkHaskell "demangler" self { inherit sayable; };
            });
      };
}
