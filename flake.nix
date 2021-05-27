{
  inputs.utils.url = "github:numtide/flake-utils";
  inputs.devshell.url = "github:numtide/devshell";
  outputs = {nixpkgs, utils, devshell, ... }:
    utils.lib.eachSystem ["x86_64-linux"] (system:
      let
        pkgs = import "${nixpkgs}" {
          inherit system;
          config.allowUnfree = true;
          overlays = [
            devshell.overlay
            (final: prev: {
              python3 = prev.python3.override {
                self = prev.python3;
                packageOverrides = finalpy: prevpy: {
                  pystan = prevpy.buildPythonPackage rec {
                    pname = "pystan";
                    version = "2.19.1.1";
                    name = "${pname}-${version}";
                    src = prevpy.fetchPypi {
                      inherit pname version;
                      sha256 = "0f5hbv9dhsx3b5yn5kpq5pwi1kxzmg4mdbrndyz2p8hdpj6sv2zs";
                    };
                    propagatedBuildInputs = with prevpy; [ cython numpy matplotlib ];
                    doCheck = false; # long, slow tests
                  };
                };
              };
            })
          ];

        };
      in
      rec {
       devShell = pkgs.devshell.mkShell {
          packages = with pkgs; [
            watchexec
            cmdstan
            (python3.withPackages (ps: [ps.pystan]))
          ];
          # hack for zsh devshell
          bash.interactive = (pkgs.lib.optionalString true ''
            temp_dir=$(mktemp -d)
            cat <<'EOF' >"$temp_dir/.zshrc"
            if [ -e ~/.zshrc ]; then . ~/.zshrc; fi
            if [ -e ~/.config/zsh/.zshrc ]; then . ~/.config/zsh/.zshrc; fi
            menu
            EOF
            ZDOTDIR=$temp_dir zsh -i
          '');
          commands = let
            watchexec = "${pkgs.watchexec}/bin/watchexec";
          in [
            {
              category = "watchers";
              name = "watch-stan";
              command = ''
                ${watchexec} -e v "make -j && make install && ( ./out/bin/ccomp -c $1 && echo '>>> done.' || echo '>>> error!' )"
              '';
            }
          ];
        };
      });
}
