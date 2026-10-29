{
  # Pinned to NixOS/nixpkgs#573940 (vsrocq 2.5.0) until it reaches nixos-unstable.
  inputs.nixpkgs.url = "github:Zimmi48/nixpkgs/15aabc6e8d56a08f7d2f8dcc94c9b0a251aa1e45";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # Function to override versions of rocq packages. This function takes two arguments:
      # - rocqPackages: The set of all Rocq packages.
      # - versions: An attribute set of packages with their versions we want to override.
      patchRocqPackages = rocqPackages: versions:
        rocqPackages.overrideScope (
          self: super:
            pkgs.lib.foldlAttrs
              # foldAttrs is used to iterate over the versions set and apply a function
              # to each attribute. This function takes three arguments: the accumulator set,
              # the attribute name (package name), and the attribute value (version).
              (acc: pkg: version:
                # This function returns a new set with the current attribute added to the
                # accumulator set. The attribute name is the package name, and the value
                # is the overridden package.
                acc // { ${pkg} = super.${pkg}.override { inherit version; }; })
              # The initial value of the accumulator set. We add our own package here.
              { katamaran = self.callPackage ./default.nix { }; }
              # The attribute set to iterate over.
              versions
        );

      iris45 = {
        iris = "4.5.0";
        stdpp = "1.13.0";
      };

      # Rocq that hash-conses functor parameters and Includes: .vo files ~3x
      # smaller, peak memory ~30% lower here.
      hashcons = rocqPackages: rocqPackages.overrideScope (self: super: {
        rocq-core = super.rocq-core.overrideAttrs (old: {
          patches = (old.patches or [ ]) ++ [ ./nix/rocq-hashcons-modules.patch ];
        });
      });

      rocqPackages920 = patchRocqPackages (hashcons pkgs.rocqPackages_9_2) iris45;
      rocqPackages930 = patchRocqPackages (hashcons pkgs.rocqPackages_9_3) iris45;

      # rocq-lsp (provides `pet`); nixpkgs only has it up to Rocq 9.1.
      rocqLsp920 =
        let ocamlPackages = rocqPackages920.rocq-core.ocamlPackages; in
        ocamlPackages.buildDunePackage {
          pname = "coq-lsp";
          version = "0.2.5-unstable-v9.2";
          src = pkgs.fetchFromGitHub {
            owner = "rocq-community";
            repo = "rocq-lsp";
            rev = "f49d7b391c8dc6599a00d126d7bfedc9efbdc2e7"; # branch v9.2
            hash = "sha256-VJLe7zNcvbUN0QsA/cKuhyr6kHKGWDf9Wp8uFhHQGvw=";
          };
          nativeBuildInputs = [ ocamlPackages.menhir ];
          buildInputs = [ rocqPackages920.rocq-core ];
          propagatedBuildInputs = with ocamlPackages; [
            cmdliner
            dune-build-info
            findlib
            logs
            lwt
            ppx_compare
            ppx_deriving
            ppx_deriving_yojson
            ppx_hash
            ppx_import
            ppx_inline_test
            ppx_sexp_conv
            sexplib
            tyxml
            uri
            yojson
            zarith
          ];
          meta = {
            description = "Language server and petanque (pet) for the Rocq prover";
            homepage = "https://github.com/rocq-community/rocq-lsp";
            license = pkgs.lib.licenses.lgpl21Plus;
          };
        };

      # rocq-devtools (provides `rocq timelog2html`); not packaged in nixpkgs.
      rocqDevtools920 =
        let
          rocq-core = rocqPackages920.rocq-core;
          ocamlPackages = rocq-core.ocamlPackages;
        in
        pkgs.stdenv.mkDerivation {
          pname = "rocq-devtools";
          inherit (rocq-core) version src;
          nativeBuildInputs = [ ocamlPackages.ocaml ocamlPackages.findlib pkgs.dune ];
          buildInputs = [ rocq-core ] ++ (with ocamlPackages; [ camlzip yojson zarith ]);
          dontConfigure = true;
          buildPhase = ''
            runHook preBuild
            dune build -p rocq-devtools -j $NIX_BUILD_CORES
            runHook postBuild
          '';
          # `rocq timelog2html` looks up the executable via findlib.
          installPhase = ''
            runHook preInstall
            dune install --prefix $out \
              --libdir $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib rocq-devtools
            runHook postInstall
          '';
          strictDeps = true;
          meta = {
            description = "Development tools for the Rocq prover (timelog2html)";
            homepage = "https://rocq-prover.org";
            license = pkgs.lib.licenses.lgpl21Only;
          };
        };
    in
    rec {
      packages = rec {
        default = rocq920;
        rocq920 = rocqPackages920.katamaran;
        rocq930 = rocqPackages930.katamaran;

        rocq-lsp-rocq920 = rocqLsp920;
        rocq-devtools-rocq920 = rocqDevtools920;
      };

      # Editor/agent tooling. No default dev shell on purpose, so plain
      # `nix develop` stays the build environment.
      devShells.lsp = pkgs.mkShell {
        inputsFrom = [ rocqPackages920.katamaran ];
        packages = [
          rocqPackages920.rocq-core
          rocqPackages920.vsrocq-language-server
          rocqLsp920
          rocqDevtools920
          # For `dune build`; the same OCaml and dune Rocq is built with.
          rocqPackages920.rocq-core.ocamlPackages.ocaml
          rocqPackages920.rocq-core.ocamlPackages.dune_3
        ];
      };
    }
  );
}
