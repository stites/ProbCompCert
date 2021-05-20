{
  inputs.utils.url = "github:numtide/flake-utils";
  inputs.devshell.url = "github:numtide/devshell";
  outputs = {nixpkgs, utils, devshell, ... }:
    utils.lib.eachSystem ["x86_64-linux"] (system:
      let
        pkgs = import "${nixpkgs}" {
          inherit system;
          config.allowUnfree = true;
          overlays = [ devshell.overlay ];
        };
      in
      rec {
       devShell = pkgs.devshell.mkShell {
          packages = with pkgs; [
            watchexec
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
              command = ''${watchexec} -e v "make -j && make install && ./out/bin/ccomp $1"'';
            }
          ];
        };
      });
}
