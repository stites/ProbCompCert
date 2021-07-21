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
            run = {build ? null, cmd, finally ? null}:
              let
                err-str = if finally == null then cmd else "${cmd}, attempting ${finally}...";
                final-cmd = if finally == null then "" else "&& ${finally}";
                runnable = "${cmd} && echo '>>> done: ${cmd}.' || ( echo '>>> error! ${err-str}' ${final-cmd})";
              in if build == null then runnable else "${build} && (${runnable})";

            watch = {at-root ? true, exts ? "v,ml,stan,c,Makefile", build ? null, cmd, finally ? null}: ''
              ${if at-root then cd-root else ""}
              if [ -z "$1" ]; then
                  ignore=""
              else
                  ignore="--ignore $name.v"
              fi
              ${watchexec} -e ${exts} $ignore "${run {inherit build cmd finally; }}"
             '';
            mk-watcher = name: all@{ ... }: all // { inherit name; category = "watchers"; };

          in [
            (mk-watcher "watch-stan" {
              command = watch {
                build = "make -j && make install";
                cmd = "./out/bin/ccomp -c $current_dir/$1";
              };
            })
            (mk-watcher "watch-stan-debug" {
              command = watch {
                build = "make -j && make install";
                cmd = "./out/bin/ccomp -c $current_dir/$1";
                finally = "./out/bin/clightgen $current_dir/$1";
              };
            })
            (mk-watcher "watch-clightgen" {
              command = watch {
                build = "make -j clightgen";
                cmd = "./clightgen $current_dir/$1";
              };
            })
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
              category = "build";
              name = "ccompstan";
              command = ''
                ${cd-root}
                cd stanfrontend
                ccomp -c $current_dir/$1
                ccomp -c ''${name}.s
                ccomp -c Runtime.c
                ccomp -c stanlib.c
                ld -shared stanlib.o -o libstan.so
                ccomp -L''${stan_dir} -Wl,-rpath=''${stan_dir} -L../out/lib/compcert -lm -lstan ''${name}.o Runtime.o -o runit
                echo "compiled! ./stanfrontend/runit [int]"
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
