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
            gcc
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
            cd-root = ''
              current_dir=$PWD
              root_dir=$(${pkgs.git}/bin/git rev-parse --show-toplevel)
              stan_dir=$root_dir/stanfrontend
              prog=''${1##*/}
              name=''${prog%.*}
              parent_dir="$(dirname -- "$(readlink -f -- "$1")")"
              cd $root_dir
            '';
          in [
            {
              category = "watchers";
              name = "watch-stan";
              command = ''
                ${cd-root}
                ${watchexec} -e v,ml,Makefile "make -j && make install && ( ./out/bin/ccomp -c $current_dir/$1 && echo '>>> done.' || echo '>>> error!' )"
              '';
            }
            {
              category = "watchers";
              name = "watch-clightgen";
              command = ''
                ${cd-root}
                ${watchexec} -e v,ml,Makefile "make -j clightgen"
              '';
            }
            {
              category = "configure";
              name = "cconf64+clightgen";
              command = ''
                ${cd-root}
                ./configure -prefix ./out -clightgen x86_64-linux
              '';
            }
            {
              category = "configure";
              name = "cconf64";
              command = ''
                ${cd-root}
                ./configure -prefix ./out x86_64-linux
              '';
            }
            {
              category = "test";
              name = "test-stan";
              command = ''
                ${cd-root}
                ./out/bin/ccomp -c $current_dir/$1
              '';
            }
            {
              category = "make";
              name = "make-all";
              command = ''
                ${cd-root}
                make -j && make install
              '';
            }
            {
              category = "test";
              name = "test-c1";
              command = let
                compiler = "../out/bin/ccomp";
              in ''
                ${cd-root}
                cd stanfrontend
                ${compiler} -c Runtime.c
                ${compiler} -c Program.c
                ${compiler} -L../out/lib/compcert -lm Program.o Runtime.o -o runit
                ./runit $1
              '';
            }
            {
              category = "test";
              name = "test-c2";
              command = let
                compiler = "../out/bin/ccomp";
                program = "Program2";
              in ''
                ${cd-root}
                cd stanfrontend
                ${compiler} -c Runtime.c
                ${compiler} -c ${program}.c
                ${compiler} -c stanlib.c
                ld -shared stanlib.o -o libstan.so
                ${compiler} -L''${stan_dir} -Wl,-rpath=''${stan_dir} -L../out/lib/compcert -lm -lstan ${program}.o Runtime.o -o runit
                ./runit $1
              '';
            }
            {
              category = "test";
              name = "test-stan2";
              command = ''
                ${cd-root}
                ./out/bin/ccomp -c $current_dir/$1
                ./out/bin/ccomp -c $current_dir/$1.s
              '';
            }
            {
              category = "test";
              name = "test-stan2-full";
              command = ''
                ${cd-root}
                ./out/bin/ccomp -c $current_dir/$1
                ./out/bin/ccomp -c $current_dir/$name.s
                ./out/bin/ccomp -c $stan_dir/Runtime.c
                ./out/bin/ccomp -c $stan_dir/stanlib.c
                ld -shared $current_dir/stanlib.o -o $current_dir/libstan.so
                ./out/bin/ccomp -L''${stan_dir} -Wl,-rpath=''${stan_dir} -L./out/lib/compcert -lm -lstan $name.o Runtime.o -o runit
                ./runit $2
              '';
            }
          ];
        };
      });
}
